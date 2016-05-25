package soot.jimple.infoflow.android.ModeHandle;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import javax.xml.stream.XMLStreamException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xmlpull.v1.XmlPullParserException;

import soot.Scene;
import soot.SootMethod;
import soot.jimple.Stmt;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.InfoflowforScan;
import soot.jimple.infoflow.android.InfoflowAndroidConfiguration;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.android.manifest.ProcessManifest;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.SootMethodAndClass;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.results.xml.InfoflowResultsSerializer;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.SystemClassHandler;
import soot.options.Options;

public class ModeHandle {
	
	private final static Logger logger = LoggerFactory.getLogger(ModeHandle.class);
	private static boolean DEBUG = false;
	
	private static InfoflowAndroidConfiguration config;
	private static IIPCManager ipcManager = null;
	private static boolean aggressiveTaintWrapper = false;
	private static boolean noTaintWrapper = false;
	private static String summaryPath = "";
	private static String resultFilePath = "";
	
	
	public static void initConfig(InfoflowAndroidConfiguration config,IIPCManager ipcManager,String summaryPath,String resultFilePath,boolean aggressiveTaintWrapper,boolean noTaintWrapper)
	{
		ModeHandle.config=config;
		ModeHandle.ipcManager=ipcManager;
		ModeHandle.aggressiveTaintWrapper=aggressiveTaintWrapper;
		ModeHandle.noTaintWrapper=noTaintWrapper;
		ModeHandle.summaryPath=summaryPath;
		ModeHandle.resultFilePath=resultFilePath;
		
	}
	
	public static boolean runAnalysisonebyone(final String fileName, final String androidJar)
	{
		//输出两个文件：处理每个entrypoints的结果信息，另一个是结果集
		
		Set<String> entrypoints=null;
		
		try{
			File entryfile = new File(config.getAndroidconfig().getTestOnebyoneentrypoints());
			if(!entryfile.exists() )
			{
				ProcessManifest processMan = new ProcessManifest(fileName);
				entrypoints=processMan.getEntryPointClasses(config.getAndroidconfig().getUseEntrypointskind());
			}
			else
			{
				entrypoints=new HashSet<String>();
				readentrypoints(config.getAndroidconfig().getTestOnebyoneentrypoints(),entrypoints);
			}

			if(entrypoints.isEmpty())
			{
				logger.error("Don't find entrypoints,entrypoints init error(int Test.java)\n");
				return false;
			}
			
			
			
			SimpleDateFormat df = new SimpleDateFormat("_yyyy-MM-dd_HH_mm_ss)");//
			String time=df.format(new Date()) ;
			String resultfilename="Result_"+time+".txt";
			String errofilename="Errofile_"+time+".txt";
	
			File resultfile = new File(resultfilename);
			if(!resultfile.exists() )
			{
				resultfile.createNewFile();
			}
			
			
			
			//InfoflowResults res=null;
			for(String entry:entrypoints)
			{
				logger.info("Now,we are processing entrypoints : "+entry+"\n");
				try{
						tryrunAnalysis(fileName,androidJar,entry,resultfilename);
						System.gc();
				}catch(RuntimeException e)
		        {
					e.printStackTrace();
					writeError(e,entry,null,null,errofilename);
		        	System.gc();
		        	continue;
		        }
				
			}
			writeresult(null,null,resultfilename,null,null);
			
		}catch (IOException | XmlPullParserException e){
			System.out.println("preparing result file error!");
			e.printStackTrace();
			return false;
		} 
		return true;
	}
	
	public static void tryrunAnalysis(final String fileName, final String androidJar,String entrypoint,String resultfilename) 
	{
		
		try {

			SetupApplication app=getSimpleApp(androidJar,fileName,null);
			app.setCurrententrypoints(entrypoint);
			app.calculateSourcesSinksEntrypoints("SourcesAndSinks.txt");
		
			if (DEBUG) {
				app.printEntrypoints();
				app.printSinks();
				app.printSources();
			}
			
			System.out.println("Running data flow analysis...");
			InfoflowResults res=null;
			//罗丹修改：删除回调注册
			if(config.getConfig().isUsingChange() ||config.getConfig().isJustPrintresultnum())
			{
				res=app.runInfoflow();
				writeresult(entrypoint,res,resultfilename,null,String.valueOf(app.getMaxMemoryConsumption()));
		        res=null;
			}
			else
			{
				res=app.runInfoflow(new MyResultsAvailableHandler());;
				writeresult(entrypoint,res,resultfilename,null,String.valueOf(app.getMaxMemoryConsumption()));
				res=null;
			}
			
		} catch (IOException ex) {
			System.err.println("Could not read file: " + ex.getMessage());
			ex.printStackTrace();
			
		} catch (XmlPullParserException ex) {
			System.err.println("Could not read Android manifest file: " + ex.getMessage());
			ex.printStackTrace();
			
		}

	}
	
	public static Set<String> lookingEntrypointsAndCallbackOnebyone(String apkname,String androidjar)
	{
		logger.info("lookingEntrypointsAndCallbackOnebyone\n");
		
        Stack<String> entrypoints=new Stack<String>();
        Set<String> newentrypoints=new HashSet<String>();
        Set<String> allEntry=new HashSet<String>();
		try{
			
	        //only broadcast can be dynamic declare in program code,so entrypoints has most of entrypoints
			ProcessManifest processMan = new ProcessManifest(apkname);
	       
	        entrypoints.addAll(processMan.getEntryPointClasses(config.getAndroidconfig().getUseEntrypointskind()) );
	       
	        if(entrypoints.isEmpty())
			{
				System.out.println("Don't find entrypoints,entrypoints init error(int Test.java)\n");
				return null;
			}
	        allEntry.addAll(entrypoints);
			
			
			SetupApplication app;
			SimpleDateFormat df = new SimpleDateFormat("_yyyy-MM-dd(HH_mm_ss)");//
			String time=df.format(new Date()) ;
			String resultfilename="Looking_entry_cb_Results"+time+".txt";
			//String entrypointsresultname="Entrypoints_plus_allBroadcast_"+time+".txt";
		    String  allEntryfile="all_entry_format"+time+".txt";
				while(!entrypoints.isEmpty())
				{
					
					String currentpoints=entrypoints.pop();
					app=new SetupApplication(androidjar, apkname);
					Set<String>  newBroadcast=app.calculateEntrypoints(currentpoints);
					newentrypoints.addAll(newBroadcast);
					writeAppInfoToFile(resultfilename,app,currentpoints,newBroadcast);
					
				}
				
				
				allEntry.addAll(newentrypoints);
			    writeColloections(allEntry,allEntryfile);
		        logger.info("\r\n\r\n LookingEntrypointsAndCallbackOnebyone had done! ");
			
		}catch (IOException | XmlPullParserException e){
			System.out.println("preparing result file error!");
			e.printStackTrace();
			return null;
		}
		
		return allEntry;
	}
	//fly
	public static boolean scanAndSaveSource(final String apkname,final String androidjar){
		try{
			SetupApplication app = new SetupApplication(androidjar,apkname);
			app.setConfig(config);
			
			if (noTaintWrapper)
				app.setSootConfig(new IInfoflowConfig() {
					
					@Override
					public void setSootOptions(Options options) {
						options.set_include_all(true);
					}
					
				});
			
			final ITaintPropagationWrapper taintWrapper;
			if (noTaintWrapper)
				taintWrapper = null;
			else if (summaryPath != null && !summaryPath.isEmpty()) {
				System.out.println("Using the StubDroid taint wrapper");
				taintWrapper = createLibrarySummaryTW();
				if (taintWrapper == null) {
					System.err.println("Could not initialize StubDroid");
					return false;
				}
			}
			else {
				final EasyTaintWrapper easyTaintWrapper;
				if (new File("../soot-infoflow/EasyTaintWrapperSource.txt").exists())
					easyTaintWrapper = new EasyTaintWrapper("../soot-infoflow/EasyTaintWrapperSource.txt");
				else
					easyTaintWrapper = new EasyTaintWrapper("EasyTaintWrapperSource.txt");
				easyTaintWrapper.setAggressiveMode(aggressiveTaintWrapper);
				taintWrapper = easyTaintWrapper;
			}
			app.setTaintWrapper(taintWrapper);
			
			app.calculateSourcesSinksEntrypoints("SourcesAndSinks.txt");
			Map<String,Set<String>> SourceMap=app.runInfoflowScan();
			return saveSourceMethod(SourceMap);
		}catch (Exception e){
			System.out.println("write in source file error!");
			e.printStackTrace();
			return false;
		}
		
	}

	
	//fly save source method result to .txt
	private static boolean saveSourceMethod(Map<String, Set<String>> sourceMp){
		try{
			File sourcef= new File("SourceSelect.txt");
			if(!sourcef.exists()){
				sourcef.createNewFile();
				System.out.print("SourceSelect.txt is not exit,Auto-create one");
			}
			
			FileWriter fw= new FileWriter(sourcef);
			BufferedWriter bf = new BufferedWriter(fw);
			for(String locationMethod: sourceMp.keySet()){
				bf.write("--"+locationMethod);
				bf.newLine();
				
				Set<String> source = sourceMp.get(locationMethod);
				for(String sourceMethod:source){
					bf.write(sourceMethod);
					bf.newLine();
				}
				bf.newLine();
				bf.newLine();
				
			}	
			bf.close();

		}catch(Exception e){
			System.out.print("unsuccessfully write in");
			e.printStackTrace();
		}
		return true;
	}
	//fly 
	
	//fly change
	public static boolean setSource(){
		Map<String,Set<String>> sourceMp = getSourceMethod();
		if(sourceMp.isEmpty()){
			System.err.println("you did not select any source method as InitialSeed in SourceAndSinks.txt");
			return false;
		}
		Infoflow.setSource(sourceMp);
		return true;
	}
	
	private static Map<String,Set<String>> getSourceMethod(){
			
			String locationMethod=" ";
			Map<String,Set<String>> sourceMp=new HashMap<String,Set<String>>();
			
			try{
				File f= new File("SourceSelect.txt");
				if(!f.exists()){
					System.out.print("SourceSelect.txt is not exit");
					throw new IOException();
				}
				
				FileReader fr= new FileReader(f);
				BufferedReader br = new BufferedReader(fr);
				
				String readline;
				while((readline=br.readLine())!=null){
					if(readline.startsWith("--")){
						locationMethod=readline.substring(2);
					}else if(!readline.isEmpty()){
						if(sourceMp.get(locationMethod)==null)
		        		{
		        			Set<String> methodSigs = new HashSet<String>();
		        			sourceMp.put(locationMethod, methodSigs);
		        		}
		        		sourceMp.get(locationMethod).add(readline);
					}
				}
				
				br.close();
				
			}catch(Exception e){
				System.out.print("unsuccessfully read source file");
				e.printStackTrace();
			}
			
			return sourceMp;
		}
	//fly
	
	/*public static boolean runOneEntrypointsPlusXCallbacks(String apkname,String androidjar)
	{
		logger.error("runOneEntrypointsPlusXCallbacks in step:"+config.getAndroidconfig().getCallbackstep());
		
		try{
	        //only broadcast can be dynamic declare in program code,so entrypoints has most of entrypoints
	        ProcessManifest processMan = new ProcessManifest(apkname);
	        Stack<String> entrypoints=new Stack<String>();
	        
	        entrypoints.addAll(processMan.getEntryPointClasses(config.getAndroidconfig().getUseEntrypointskind()) );
	        
	        if(entrypoints.isEmpty())
			{
				System.out.println("Don't find entrypoints,entrypoints init error(int Test.java)\n");
				return false;
			}
        
			
	       //  config.setLayoutMatchingMode(LayoutMatchingMode.MatchAll);
	       // config.setLayoutMatchingMode(LayoutMatchingMode.MatchSensitiveOnly);
			SetupApplication app;
			
			SimpleDateFormat df = new SimpleDateFormat("_yyyy-MM-dd(HH_mm_ss)");//
			String time=df.format(new Date()) ;
			String callbacksresultfilename="EntrypointsAndCallbacks"+time+".txt";
			String entrypointsresultname="Entrypointscollected_plus_allBroadcast_"+time+".txt";
			String resultfilename="run_Xstep_Results"+time+".txt";
			String errofilename="run_Xstep__erro"+time+".txt";
			while(!entrypoints.isEmpty())
			{
				app=new SetupApplication(androidjar, apkname);
				String currentpoints=entrypoints.pop();
				Set<String> newBroadcast=app.calculateEntrypoints(currentpoints);
				
				runXCallbacks(androidjar,apkname,app,currentpoints,newBroadcast,config.getAndroidconfig().getCallbackstep(),resultfilename,errofilename);
				
				writeAppInfoToFile(callbacksresultfilename,app,currentpoints,newBroadcast);
			}
			
			
		   System.out.println("\r\n\r\n runOneEntrypointsAndXCallbacks had done! ");
			
		}catch (IOException | XmlPullParserException e){
			System.out.println("preparing result file error!");
			e.printStackTrace();
			return false;
		}
		
		
		return true;
	}*/
	
	
	/*public static void runXCallbacks(String androidjar,String apkname,SetupApplication originalapp,String currentpoints,Set<String> newBroadcast,int step,String resultfilename,String errofilename)
	{
		
		  try {

					Stack<SootMethodAndClass> callbacks=new Stack<SootMethodAndClass>();
					if(originalapp.getCallbackMethods().get(currentpoints)!=null)
					{
						//printmap(originalapp.getCallbackMethods());
						callbacks.addAll(originalapp.getCallbackMethods().get(currentpoints) );
					}
					
					
					
				
					do
				    {
						InfoflowResults res;
						SetupApplication app=getSimpleApp(androidjar,apkname,originalapp.getAppPackageName());
						Set<SootMethodAndClass> tempcallbacks = popXelement(callbacks,step);	
						Map<String,Set<SootMethodAndClass>> cb=new HashMap<String,Set<SootMethodAndClass>>();
						cb.put(currentpoints, tempcallbacks);
						Iterator<String> it=newBroadcast.iterator();
						while(it.hasNext())
						{
							String en= it.next();
							cb.put(en, originalapp.getCallbackMethods().get(en));
						}
						Set<String> entryponts=new HashSet<String>();
						entryponts.add(currentpoints);
						entryponts.addAll(newBroadcast);
						
						app.setEntrypoints(entryponts);
						app.setCallbackMethods(cb);
						
						
						app.calculateSourcesSinksEntrypoints_version2("SourcesAndSinks.txt");
						System.out.println("Now We are processing entrypoints "+currentpoints+" In testOneEntrypointsAndXcallbacks mode");
						System.out.println("---------Before runInfoflow----------------");
						
						try{
						   res=app.runInfoflow(new MyResultsAvailableHandler());
				        }catch(Exception e)
				        {
				        	writeError(e,currentpoints,newBroadcast,tempcallbacks,errofilename);
				        	res=null;
				        	app=null;
				        	System.gc();
				        	continue;
				        }
				        
						System.out.println("---------After runInfoflow----------------");
						if(res==null)
						{
							System.out.println("current entrypoints "+currentpoints+" does not have Results!");
						}
						else
						{
							System.out.println("current entrypoints "+currentpoints+" have found Results!");
						}
						writeresult(currentpoints,res,resultfilename,tempcallbacks,String.valueOf(app.getMaxMemoryConsumption()));
						res=null;
						app.getCallbackMethods().clear();
						app.getEntrypoints().clear();
						cb.clear();
						
						System.gc();
					}
					while(!callbacks.isEmpty());
	
		   
		   }catch (IOException ex) {
				System.err.println("Could not read file: " + ex.getMessage());
				ex.printStackTrace();
				throw new RuntimeException(ex);
			} catch (XmlPullParserException ex) {
				System.err.println("Could not read Android manifest file: " + ex.getMessage());
				ex.printStackTrace();
				throw new RuntimeException(ex);
			}

		
		
	}*/

	
	//注释
	/*public static boolean runOneEntrypointsPlusXCallbacks(String apkname,String androidjar)
	{
		System.err.println("runOneEntrypointsPlusXCallbacks in step:"+config.getCallbackstep());
		
		try{
	        //only broadcast can be dynamic declare in program code,so entrypoints has most of entrypoints
	        ProcessManifest processMan = new ProcessManifest(apkname);
	        Stack<String> entrypoints=new Stack<String>();
	        Set<String>newentrypoints=new HashSet<String>();
	        entrypoints.addAll(processMan.getEntryPointClasses(config.getUseEntrypointskind()) );
	        
	        if(entrypoints.isEmpty())
			{
				System.out.println("Don't find entrypoints,entrypoints init error(int Test.java)\n");
				return false;
			}
        
			
			
			SetupApplication app;
			
			SimpleDateFormat df = new SimpleDateFormat("_yyyy-MM-dd(HH_mm_ss)");//
			String time=df.format(new Date()) ;
			String callbacksresultfilename="LookingEntrypointsAndCallbacksResults"+time+".txt";
			String entrypointsresultname="Entrypointscollected_plus_allBroadcast_"+time+".txt";
			String resultfilename="runOneEntrypointsPlusXCallbacksResults"+time+".txt";
			
			while(!entrypoints.isEmpty())
			{
				app=new SetupApplication(androidjar, apkname);
				String currentpoints=entrypoints.pop();
				Set<String> newBroadcast=app.calculateEntrypoints(currentpoints);
				
				newentrypoints.add(currentpoints);
				newentrypoints.addAll(newBroadcast);
				
				writeAppInfoToFile(callbacksresultfilename,entrypointsresultname,app,currentpoints,newBroadcast);
			}
			entrypoints.addAll(newentrypoints);//添加到stack的后头
			
			while(!entrypoints.isEmpty())
			{
				String currentpoints=entrypoints.pop();
				runCallbacksStep(apkname,androidjar,resultfilename,currentpoints,config.getCallbackstep());
			}
			
			
		   System.out.println("\r\n\r\n runOneEntrypointsAndXCallbacks had done! ");
			
		}catch (IOException | XmlPullParserException e){
			System.out.println("preparing result file error!");
			e.printStackTrace();
			return false;
		}
		
		
		return true;
	}
	*/
	
	public static boolean writeError(Exception e3,String currentpoints,Set<String> newBroadcast,Set<SootMethodAndClass>tempcallbacks,String errofilename) 
	{
		    File resultfile = new File(errofilename);
		    BufferedWriter resultbw = null;
			
			try{
				
				
				if(!resultfile.exists() )
				{
					resultfile.createNewFile();
				}
				resultbw = new BufferedWriter(new FileWriter(resultfile,true));
				
				resultbw.append("----------------------------\n");
				resultbw.newLine();
				resultbw.append("entry:"+currentpoints);
				resultbw.newLine();
				
				if(e3.getMessage()!=null)
				{
					resultbw.append("exception msg:"+e3.getMessage());
					resultbw.newLine();
				}
				
				
				StackTraceElement[] stacks = e3.getStackTrace();
				if(stacks!=null)
			    {
					for(StackTraceElement s: stacks)
				    {
						    resultbw.append("   at"+s.toString());
				            resultbw.newLine();
				    }
			    }
				
				Throwable cause=e3.getCause();
				if(cause!=null&&cause.getMessage()!=null)
				{
					resultbw.append("cause by :"+cause.getMessage());
					resultbw.newLine();
				}
				
				
				resultbw.append("The detail info of the cause :");
				resultbw.newLine();
				if(cause!=null)
				{
								
					StackTraceElement[] stacks2 = cause.getStackTrace();
					if(stacks!=null)
				        for(StackTraceElement s: stacks2)
				        {
				        	resultbw.append("   at:"+s.toString());
				            resultbw.newLine();
				        }
				
				}
				if(newBroadcast!=null)
					resultbw.append( newBroadcast.toString());
				
				if(tempcallbacks!=null)
				{
					resultbw.append("\n There are callbacks: ");
					resultbw.newLine();
					Iterator<SootMethodAndClass>it =tempcallbacks.iterator();
					while(it.hasNext())
					{
						resultbw.newLine();resultbw.append("      ");
						resultbw.append(it.next().getSignature());
					}
				}
				
				
				resultbw.newLine();
				resultbw.append("\r\n");
			}catch(NullPointerException e1)
			{
				try {
					resultbw.newLine();
					resultbw.append("We have encountered and NullPointerException while we print erro info into file! ->In ModeHandle.java");
					e1.printStackTrace();
				} catch (IOException e) {
					e.printStackTrace();
				}
				return false;
			}catch(Exception e2)
			{
				
				try {
					resultbw.newLine();
					resultbw.append("We have encountered an Exception while we print erro info into file! ->In ModeHandle.java");
					e3.printStackTrace();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				return false;
			}
			finally
			{
				try {
					resultbw.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
			}
		return true;
	}
	
	//只查找entrypoints and callbacks
	
	
	public static boolean writeAppInfoToFile(String resultfilename,SetupApplication app,String currentpoints,Set newBroadcast)
	{
		
		
		File resultfile = new File(resultfilename);
		BufferedWriter resultbw=null;
		
		try{
			
			resultbw = new BufferedWriter(new FileWriter(resultfile,true));
			if(!resultfile.exists() )
			{
				resultfile.createNewFile();
			}
	
			resultbw.newLine();
			resultbw.append(currentpoints);
			
			if(!app.getCallbackMethods().isEmpty())
			{
				resultbw.newLine();resultbw.append("--"+currentpoints);
				for(SootMethodAndClass entry :app.getCallbackMethods().get(currentpoints))
				{
					resultbw.newLine();resultbw.write(entry.getSignature());
				}
				
				resultbw.append("--end of callbacks");resultbw.newLine();
			}
			
			
		}catch(Exception e)
		{
			System.out.println("Print setupapplication info error !");
			e.printStackTrace();
			return false;
		}finally
		{
			
			try {
				resultbw.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		}
		return true;
	}
	public static boolean writeColloections(Set<String> set,String filename)
	{
		File resultfile = new File(filename);
		BufferedWriter resultbw=null;
		
		try{
			
			resultbw = new BufferedWriter(new FileWriter(resultfile,true));
			
			if(!resultfile.exists() )
			{
				resultfile.createNewFile();
			}
		
			
			if(!set.isEmpty())
			{
				for(String string :set)
				{
					resultbw.append(string);
					resultbw.newLine();
				}
				
			}
			
			
		}catch(Exception e)
		{
			System.out.println("Print setupapplication info error !");
			e.printStackTrace();
			return false;
		}finally
		{
			
			try {
				resultbw.close();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		}
		return true;
	}
	public static  void printmap(Map<String, Set<SootMethodAndClass>>  map)
	{
		System.err.println("\n-----------------------------------\n");
		for(String key:map.keySet())
		{
			for(SootMethodAndClass sm:map.get(key))
			{
				System.out.println(key+":"+sm.getSignature());
			}
		}
		System.err.println("\n-----------------------------------\n");
	}
	
	public static SetupApplication getSimpleApp(String androidjar,String apkname,String appPackageName) throws IOException{
		final SetupApplication app;
		
		if (null == ipcManager)
		{
			app = new SetupApplication(androidjar, apkname);
		}
		else
		{
			app = new SetupApplication(androidjar, apkname, ipcManager);
		}
		
		// Set configuration object
		app.setConfig(config);
		
		final ITaintPropagationWrapper taintWrapper;
		if (noTaintWrapper)
			taintWrapper = null;
		else if (summaryPath != null && !summaryPath.isEmpty()) {
			System.out.println("Using the StubDroid taint wrapper");
			taintWrapper = createLibrarySummaryTW();
			if (taintWrapper == null) {
				System.err.println("Could not initialize StubDroid");
				return null;
			}
		}
		else {
			final EasyTaintWrapper easyTaintWrapper;
			if (new File("../soot-infoflow/EasyTaintWrapperSource.txt").exists())
				easyTaintWrapper = new EasyTaintWrapper("../soot-infoflow/EasyTaintWrapperSource.txt");
			else
				easyTaintWrapper = new EasyTaintWrapper("EasyTaintWrapperSource.txt");
			easyTaintWrapper.setAggressiveMode(aggressiveTaintWrapper);
			taintWrapper = easyTaintWrapper;
		}
		app.setTaintWrapper(taintWrapper);
		if(appPackageName!=null)
		   app.setAppPackageName(appPackageName);
		
		return app;
		
	}
	
	


	public static Set<SootMethodAndClass> popXelement(Stack stack,int step)
	{
		Set<SootMethodAndClass> tempcallbacks = new HashSet<>();
		while(step>0)
		{
			if(!stack.isEmpty())
				tempcallbacks.add( (SootMethodAndClass) stack.pop() );
			else
				return tempcallbacks; 
			step--;
		}
		
		return tempcallbacks;
	}
	
	public static boolean writeresult(String entry,InfoflowResults res,String resultfilename,Set<SootMethodAndClass> tempcallbacks,String addtionalstring)
	{
		File resultfile ;
		BufferedWriter resultbw;
		
		try{
			
			resultfile= new File(resultfilename);
			resultbw = new BufferedWriter(new FileWriter(resultfile,true));
			
			if(entry==null)
			{
				resultbw.append("We have tested all entrypoints Now !\r\n");
				resultbw.close();
				return true;
			}
			
			
			resultbw.append("Now have tested entry:"+entry);
			
			if(tempcallbacks!=null && !tempcallbacks.isEmpty())
			{
				resultbw.newLine();
				resultbw.append("  entrypoints's callbacks:");
				resultbw.newLine();
				Iterator<SootMethodAndClass>it=tempcallbacks.iterator();
				while(it.hasNext())
				{
					resultbw.append(it.next().getSignature());
				}
			}
			
			resultbw.newLine();
			if(res==null)
			{
				resultbw.append("  No sink or Source find");
			}
			else if(res.getResults().size()==0)
			{
				resultbw.append("  No Results for this entrypoints");
			}
			else
			{
				
				for (ResultSinkInfo sink : res.getResults().keySet()) {
					resultbw.append("Found a flow to sink " + sink + ", from the following sources:\n");
					resultbw.newLine();
					for (ResultSourceInfo source :  res.getResults().get(sink)) 
					{
						resultbw.append("\t- " + source.getSource() + "\n");
						if (source.getPath() != null)
							resultbw.append("\t\ton Path " + Arrays.toString(source.getPath()) + "\n");
						
					}
					
				}
				
			}
			
			if(addtionalstring!=null)
			{
				resultbw.newLine();
				resultbw.append("  Addtional info:"+addtionalstring);
			}
			resultbw.newLine();
			resultbw.append("\r\n");
			
			resultbw.close();
			return true;
		}catch(IOException e)
		{
			System.out.println("write the result error !\n");
			e.printStackTrace();
			return false;
		}
	}
	
	public static boolean readentrypoints(String filename,Set<String> entrypoints)
	{
		return readentrypoints(filename,entrypoints,config.getAndroidconfig().getUseEntrypointskind());
	}
	public static boolean readentrypoints(String filename,Set<String> entrypoints,String isuseEntrypointskind)
	{
		
        try 
        {
        	File file=new File(filename);
            if (!file.exists()) 
            {
                   System.out.println("entrypoints  definition file for test one by one  not found");
                   return false;
             }
            BufferedReader rdr = new BufferedReader(new FileReader(file));
            String line;
           
            char currenttype='A';
            while ((line = rdr.readLine()) != null)
            {
            	if(line.startsWith("#"))
            		continue;//忽略该行
            	if(line.startsWith("--"))
            	{
            		currenttype=line.charAt(2);
            		if('a'<=currenttype && currenttype<='z')
            			currenttype=(char) (currenttype-32);
            	}
            	else if (!line.isEmpty()&&isuseEntrypointskind.indexOf(currenttype)>-1)
                    entrypoints.add(line);
            }
            rdr.close();
        }catch (IOException e)
        {
        	e.printStackTrace();
        	return false;
        }
        return true;
	}

	
	
	
	/**
	 * Creates the taint wrapper for using library summaries
	 * @return The taint wrapper for using library summaries
	 * @throws IOException Thrown if one of the required files could not be read
	 */
	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static ITaintPropagationWrapper createLibrarySummaryTW()
			throws IOException {
		try {
			Class clzLazySummary = Class.forName("soot.jimple.infoflow.methodSummary.data.summary.LazySummary");
			
			Object lazySummary = clzLazySummary.getConstructor(File.class).newInstance(new File(summaryPath));
			
			ITaintPropagationWrapper summaryWrapper = (ITaintPropagationWrapper) Class.forName
					("soot.jimple.infoflow.methodSummary.taintWrappers.SummaryTaintWrapper").getConstructor
					(clzLazySummary).newInstance(lazySummary);
			
			ITaintPropagationWrapper systemClassWrapper = new ITaintPropagationWrapper() {
				
				private ITaintPropagationWrapper wrapper = new EasyTaintWrapper("EasyTaintWrapperSource.txt");
				
				private boolean isSystemClass(Stmt stmt) {
					if (stmt.containsInvokeExpr())
						return SystemClassHandler.isClassInSystemPackage(
								stmt.getInvokeExpr().getMethod().getDeclaringClass().getName());
					return false;
				}
				
				@Override
				public boolean supportsCallee(Stmt callSite) {
					return isSystemClass(callSite) && wrapper.supportsCallee(callSite);
				}
				
				@Override
				public boolean supportsCallee(SootMethod method) {
					return SystemClassHandler.isClassInSystemPackage(method.getDeclaringClass().getName())
							&& wrapper.supportsCallee(method);
				}
				
				@Override
				public boolean isExclusive(Stmt stmt, Abstraction taintedPath) {
					return isSystemClass(stmt) && wrapper.isExclusive(stmt, taintedPath);
				}
				
				@Override
				public void initialize(InfoflowManager manager) {
					wrapper.initialize(manager);
				}
				
				@Override
				public int getWrapperMisses() {
					return 0;
				}
				
				@Override
				public int getWrapperHits() {
					return 0;
				}
				
				@Override
				public Set<Abstraction> getTaintsForMethod(Stmt stmt, Abstraction d1,
						Abstraction taintedPath) {
					if (!isSystemClass(stmt))
						return null;
					return wrapper.getTaintsForMethod(stmt, d1, taintedPath);
				}
				
				@Override
				public Set<Abstraction> getAliasesForMethod(Stmt stmt, Abstraction d1,
						Abstraction taintedPath) {
					if (!isSystemClass(stmt))
						return null;
					return wrapper.getAliasesForMethod(stmt, d1, taintedPath);
				}
				
			};
			
			Method setFallbackMethod = summaryWrapper.getClass().getMethod("setFallbackTaintWrapper",
					ITaintPropagationWrapper.class);
			setFallbackMethod.invoke(summaryWrapper, systemClassWrapper);
			
			return summaryWrapper;
		}
		catch (ClassNotFoundException | NoSuchMethodException ex) {
			System.err.println("Could not find library summary classes: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
		catch (InvocationTargetException ex) {
			System.err.println("Could not initialize library summaries: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
		catch (IllegalAccessException | InstantiationException ex) {
			System.err.println("Internal error in library summary initialization: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
	}

	
	private static final class MyResultsAvailableHandler implements
			ResultsAvailableHandler {
		private final BufferedWriter wr;
		
		private MyResultsAvailableHandler() {
			this.wr = null;
		}
		
		private MyResultsAvailableHandler(BufferedWriter wr) {
			this.wr = wr;
		}
		
		@Override
		public void onResultsAvailable(
				IInfoflowCFG cfg, InfoflowResults results) {
			// Dump the results
			if (results == null) {
				print("No results found.");
			}
			else {
				// Report the results
				for (ResultSinkInfo sink : results.getResults().keySet()) {
					print("Found a flow to sink " + sink + ", from the following sources:");
					for (ResultSourceInfo source : results.getResults().get(sink)) {
						print("\t- " + source.getSource() + " (in "
								+ cfg.getMethodOf(source.getSource()).getSignature()  + ")");
						if (source.getPath() != null)
							print("\t\ton Path " + Arrays.toString(source.getPath()));
					}
				}
				
				// Serialize the results if requested
				// Write the results into a file if requested
				if (resultFilePath != null && !resultFilePath.isEmpty()) {
					InfoflowResultsSerializer serializer = new InfoflowResultsSerializer(cfg);
					try {
						serializer.serialize(results, resultFilePath);
					} catch (FileNotFoundException ex) {
						System.err.println("Could not write data flow results to file: " + ex.getMessage());
						ex.printStackTrace();
						throw new RuntimeException(ex);
					} catch (XMLStreamException ex) {
						System.err.println("Could not write data flow results to file: " + ex.getMessage());
						ex.printStackTrace();
						throw new RuntimeException(ex);
					}
				}
			}
			
		}
		
			private void print(String string) {
				try {
					System.out.println(string);
					if (wr != null)
						wr.write(string + "\n");
				}
				catch (IOException ex) {
					// ignore
				}
			}
			}

	
}
