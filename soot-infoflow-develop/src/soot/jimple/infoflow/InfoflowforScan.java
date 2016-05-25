/*******************************************************************************
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/

package soot.jimple.infoflow;


import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;


import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;

import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.jimple.infoflow.cfg.BiDirICFGFactory;
import soot.jimple.infoflow.cfg.DefaultBiDiICFGFactory;
import soot.jimple.infoflow.cfg.LibraryClassPatcher;
import soot.jimple.infoflow.codeOptimization.DeadCodeEliminator;
import soot.jimple.infoflow.codeOptimization.ICodeOptimizer;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.data.AccessPathFactory;
import soot.jimple.infoflow.data.pathBuilders.IPathBuilderFactory;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.handlers.PreAnalysisHandler;
import soot.jimple.infoflow.ipc.DefaultIPCManager;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.nativ.DefaultNativeCallHandler;
import soot.jimple.infoflow.nativ.INativeCallHandler;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.SystemClassHandler;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.options.Options;
/**
 * main infoflow class which triggers the analysis and offers method to customize it.
 *
 */
public class InfoflowforScan{
	
	
	protected IPathBuilderFactory pathBuilderFactory;
	protected InfoflowConfiguration config = new InfoflowConfiguration();
	protected ITaintPropagationWrapper taintWrapper;
	protected INativeCallHandler nativeCallHandler = new DefaultNativeCallHandler();
	protected IIPCManager ipcManager = new DefaultIPCManager(new ArrayList<String>());
	
	protected final BiDirICFGFactory icfgFactory;
	protected Collection<? extends PreAnalysisHandler> preProcessors = Collections.emptyList();
	
	
	
	protected final String androidPath;
	protected final boolean forceAndroidJar;
	protected IInfoflowConfig sootConfig;
	
	//fly
	private final static Map<String, Set<String>> preInitialSeeds = new HashMap<String, Set<String>>();
	
    private final Logger logger = LoggerFactory.getLogger(getClass());
    
    private IInfoflowCFG iCfg;
    
    //fly 添加source选择控制 变量
    private boolean selectSource =false;
    
    public void setSelectSource(boolean Ss){
    	this.selectSource=Ss;
    }
    //fly
	/**
	 * Creates a new instance of the Infoflow class for analyzing Android APK files.
	 * @param androidPath If forceAndroidJar is false, this is the base directory
	 * of the platform files in the Android SDK. If forceAndroidJar is true, this
	 * is the full path of a single android.jar file.
	 * @param forceAndroidJar True if a single platform JAR file shall be forced,
	 * false if Soot shall pick the appropriate platform version
	 * @param icfgFactory The interprocedural CFG to be used by the InfoFlowProblem
	 * @param pathBuilderFactory The factory class for constructing a path builder
	 * algorithm 
	 */
	public InfoflowforScan(String androidPath, boolean forceAndroidJar, BiDirICFGFactory icfgFactory,
			IPathBuilderFactory pathBuilderFactory) {
		
		this.androidPath=androidPath;
		this.forceAndroidJar=forceAndroidJar;
		if(icfgFactory==null)
			this.icfgFactory= new DefaultBiDiICFGFactory();
		else
			this.icfgFactory=icfgFactory;
		
		this.pathBuilderFactory = pathBuilderFactory;
	}
	
	
	public Map<String, Set<String>> computeInfoflow(String appPath, String libPath,//主流程用的是这个 computeInfoflow，下面的没用 
			IEntryPointCreator entryPointCreator,
			ISourceSinkManager sourcesSinks) {
		preInitialSeeds.clear();
		if (sourcesSinks == null) {
			logger.error("Sources are empty!");
			return preInitialSeeds;
		}

		//Options.v().set_keep_line_number(true);
		initializeSoot(appPath, libPath, entryPointCreator.getRequiredClasses(),"");
		

		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		
		Scene.v().setEntryPoints(Collections.singletonList(entryPointCreator.createDummyMain()));
		
		// Run the analysis
        runAnalysis(sourcesSinks, null);//AdditionalSeeds 为空，不用添加。
        return preInitialSeeds;
	}
	
	
	/**
	 * Conducts a taint analysis on an already initialized callgraph
	 * @param sourcesSinks The sources and sinks to be used
	 */
	protected void runAnalysis(final ISourceSinkManager sourcesSinks) {
		runAnalysis(sourcesSinks, null);//没用
	}
	
	/**
	 * Conducts a taint analysis on an already initialized callgraph
	 * @param sourcesSinks The sources and sinks to be used
	 * @param additionalSeeds Additional seeds at which to create A ZERO fact
	 * even if they are not sources 特殊的开始节点
	 */
	private void runAnalysis(final ISourceSinkManager sourcesSinks, final Set<String> additionalSeeds) {
		// Clear the data from previous runs
				
		// Some configuration options do not really make sense in combination
		if (config.getEnableStaticFieldTracking()
				&& InfoflowConfiguration.getAccessPathLength() == 0)
			throw new RuntimeException("Static field tracking must be disabled "
					+ "if the access path length is zero");
		if (InfoflowConfiguration.getAccessPathLength() < 0)
			throw new RuntimeException("The access path length may not be negative");
		
		// Clear the base registrations from previous runs
		AccessPathFactory.v().clearBaseRegister();
		
		// Build the callgraph
		constructCallgraph();
		
		
        // Perform constant propagation and remove dead code
        if (config.getCodeEliminationMode() != CodeEliminationMode.NoCodeElimination) {
			eliminateDeadCode(sourcesSinks);
//			logger.info("Dead code elimination took " + (System.nanoTime() - currentMillis) / 1E9
//					+ " seconds");
        }
		try{
			iCfg = icfgFactory.buildBiDirICFG(config.getCallgraphAlgorithm(),
					config.getEnableExceptionTracking());
		}catch(Exception e){
			e.printStackTrace();
		}
	
		// We have to look through the complete program to find sources
		// which are then taken as seeds.
        
        //fly 修改开始，更改正向污点分析的 起点设置流程
        //forwardProblem.initialSeeds().clear();
	    for (SootMethod sm : getMethodsForSeeds(iCfg)){//果然是对所有的函数都搜索source sink。
	    	
	    	preScanMethodForSourcesSinks(sourcesSinks, sm);
		}
	     
        
		// We optionally also allow additional seeds to be specified
		if (additionalSeeds != null)//特殊要求的seeds 作为参数传递进来的
			for (String meth : additionalSeeds) {
				SootMethod m = Scene.v().getMethod(meth);
				if (!m.hasActiveBody()) {
//					logger.warn("Seed method {} has no active body", m);
					continue;
				}
				
				//函数的第一条unit会自动添加到种子？总数算到source里吗    改
				String sm = m.getActiveBody().getUnits().getFirst().toString();
				String ml = m.getName();
				
				if(preInitialSeeds.containsKey(sm)){
					preInitialSeeds.get(sm).addAll(Collections.singleton(ml));
				}else {
					preInitialSeeds.put(sm, new HashSet<String>(Collections.singleton(ml)));
				}
				
				//forwardProblem.addInitialSeeds(m.getActiveBody().getUnits().getFirst(),
				//		Collections.singleton(forwardProblem.zeroValue()));  //所有实函数第一条语句总是和zero绑定
			}		
	}
	
	/**
	 * Runs all code optimizers 
	 * @param sourcesSinks The SourceSinkManager
	 */
	private void eliminateDeadCode(ISourceSinkManager sourcesSinks) {
		ICodeOptimizer dce = new DeadCodeEliminator();
		dce.initialize(config);
		dce.run(iCfg, Scene.v().getEntryPoints(), sourcesSinks, taintWrapper);
	}
	

	private Collection<SootMethod> getMethodsForSeeds(IInfoflowCFG icfg) {
		List<SootMethod> seeds = new LinkedList<SootMethod>();
		// If we have a callgraph, we retrieve the reachable methods. Otherwise,
		// we have no choice but take all application methods as an approximation
		if (Scene.v().hasCallGraph()) {
			List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>(Scene.v().getEntryPoints());
			ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator(), null);
			reachableMethods.update();
			for (Iterator<MethodOrMethodContext> iter = reachableMethods.listener(); iter.hasNext();)
				seeds.add(iter.next().method());
		}
		else {
			long beforeSeedMethods = System.nanoTime();
			Set<SootMethod> doneSet = new HashSet<SootMethod>();
			for (SootMethod sm : Scene.v().getEntryPoints())
					getMethodsForSeedsIncremental(sm, doneSet, seeds, icfg);
			logger.info("Collecting seed methods took {} seconds", (System.nanoTime() - beforeSeedMethods) / 1E9);
		}
		return seeds;
	}

	private void getMethodsForSeedsIncremental(SootMethod sm,
			Set<SootMethod> doneSet, List<SootMethod> seeds, IInfoflowCFG icfg) {
		assert Scene.v().hasFastHierarchy();
		if (!sm.isConcrete() || !sm.getDeclaringClass().isApplicationClass() || !doneSet.add(sm))
			return;
		seeds.add(sm);
		for (Unit u : sm.retrieveActiveBody().getUnits()) {
			Stmt stmt = (Stmt) u;
			if (stmt.containsInvokeExpr())
				for (SootMethod callee : icfg.getCalleesOfCallAt(stmt))
					getMethodsForSeedsIncremental(callee, doneSet, seeds, icfg);
		}
	}

	/**
	 * Scans the given method for sources and sinks contained in it. Sinks are
	 * just counted, sources are added to the InfoflowProblem as seeds.
	 * @param sourcesSinks The SourceSinkManager to be used for identifying
	 * sources and sinks
	 * @param forwardProblem The InfoflowProblem in which to register the
	 * sources as seeds
	 * @param m The method to scan for sources and sinks
	 * @return The number of sinks found in this method
	 */

	/**
	 * author fly
	 * scan method for sources and sinks in advance*/
	private void preScanMethodForSourcesSinks(
			final ISourceSinkManager sourcesSinks,
			//InfoflowProblem forwardProblem,
			SootMethod m) {
		//int sinkCount = 0;
		if (m.hasActiveBody()) {
			// Check whether this is a system class we need to ignore//对于系统类的忽略在这里就有了
			final String className = m.getDeclaringClass().getName();
			if (config.getIgnoreFlowsInSystemPackages()
					&& SystemClassHandler.isClassInSystemPackage(className))
				return;
	
			// Look for a source in the method. Also look for sinks. If we
			// have no sink in the program, we don't need to perform any
			// analysis
			PatchingChain<Unit> units = m.getActiveBody().getUnits();
			for (Unit u : units) {
				Stmt s = (Stmt) u;
				if (sourcesSinks.getSourceInfo(s, iCfg) != null) {
					//String location="<"+className+">--"+"<"+m.getSignature()+">";
					String name;
					if(s.containsInvokeExpr()){
//						s.getInvokeExpr();
						name=s.getInvokeExpr().getMethod().getSignature();
					}else {
						name=s.toString();
					}
		
					
					String location=iCfg.getMethodOf(s)+"";//+"--"+s.toString();
					if(preInitialSeeds.containsKey(name)){
						preInitialSeeds.get(name).addAll(Collections.singleton(location));
					}else {
						preInitialSeeds.put(name, new HashSet<String>(Collections.singleton(location)));
					}
				}
			}
			
		}
		return;
	}
	//fly end
	
	protected void initializeSoot(String appPath, String libPath, Collection<String> classes,
			String extraSeed) {
		// reset Soot:
		//logger.info("Resetting Soot...");
		soot.G.reset();
				
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		if (logger.isDebugEnabled())
			Options.v().set_output_format(Options.output_format_jimple);
		else
			Options.v().set_output_format(Options.output_format_none);
		
		// We only need to distinguish between application and library classes
		// if we use the OnTheFly ICFG
		if (config.getCallgraphAlgorithm() == CallgraphAlgorithm.OnDemand) {
			Options.v().set_soot_classpath(libPath);
			if (appPath != null) {
				List<String> processDirs = new LinkedList<String>();
				for (String ap : appPath.split(File.pathSeparator))
					processDirs.add(ap);
				Options.v().set_process_dir(processDirs);
			}
		}
		else
			Options.v().set_soot_classpath(appendClasspath(appPath, libPath));
		
		// Configure the callgraph algorithm
		switch (config.getCallgraphAlgorithm()) {
			case AutomaticSelection:
				// If we analyze a distinct entry point which is not static,
				// SPARK fails due to the missing allocation site and we fall
				// back to CHA.
				if (extraSeed == null || extraSeed.isEmpty()) {
					Options.v().setPhaseOption("cg.spark", "on");
					Options.v().setPhaseOption("cg.spark", "string-constants:true");
				}
				else
					Options.v().setPhaseOption("cg.cha", "on");
				break;
			case CHA:
				Options.v().setPhaseOption("cg.cha", "on");
				break;
			case RTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "rta:true");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case VTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "vta:true");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case SPARK:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "string-constants:true");
				break;
			case OnDemand:
				// nothing to set here
				break;
			default:
				throw new RuntimeException("Invalid callgraph algorithm");
		}
		
		// Specify additional options required for the callgraph
		if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand) {
			Options.v().set_whole_program(true);
			Options.v().setPhaseOption("cg", "trim-clinit:false");
		}

		// do not merge variables (causes problems with PointsToSets)
		Options.v().setPhaseOption("jb.ulp", "off");
		
		if (!this.androidPath.isEmpty()) {
			Options.v().set_src_prec(Options.src_prec_apk_class_jimple);
			if (this.forceAndroidJar)
				soot.options.Options.v().set_force_android_jar(this.androidPath);
			else
				soot.options.Options.v().set_android_jars(this.androidPath);
		} else
			Options.v().set_src_prec(Options.src_prec_java);
		
		//at the end of setting: load user settings:
		if (sootConfig != null)
			sootConfig.setSootOptions(Options.v());
		
		// load all entryPoint classes with their bodies
		for (String className : classes)
			Scene.v().addBasicClass(className, SootClass.BODIES);
		Scene.v().loadNecessaryClasses();
		//logger.info("Basic class loading done.");
		
		boolean hasClasses = false;
		for (String className : classes) {
			SootClass c = Scene.v().forceResolve(className, SootClass.BODIES);
			if (c != null){
				c.setApplicationClass();
				if(!c.isPhantomClass() && !c.isPhantom())
					hasClasses = true;
			}
		}
		if (!hasClasses) {
			//logger.error("Only phantom classes loaded, skipping analysis...");
			return;
		}
	}
	
	private String appendClasspath(String appPath, String libPath) {
		String s = (appPath != null && !appPath.isEmpty()) ? appPath : "";
		
		if (libPath != null && !libPath.isEmpty()) {
			if (!s.isEmpty())
				s += File.pathSeparator;
			s += libPath;
		}
		return s;
	}
	
	protected void constructCallgraph() {
		// Allow the ICC manager to change the Soot Scene before we continue
		ipcManager.updateJimpleForICC();

		// Run the preprocessors
        for (PreAnalysisHandler tr : preProcessors)
            tr.onBeforeCallgraphConstruction();
        
        // Patch the system libraries we need for callgraph construction
        LibraryClassPatcher patcher = new LibraryClassPatcher();
        patcher.patchLibraries();
		
        // To cope with broken APK files, we convert all classes that are still
        // dangling after resolution into phantoms
        for (SootClass sc : Scene.v().getClasses())
        	if (sc.resolvingLevel() == SootClass.DANGLING) {
        		sc.setResolvingLevel(SootClass.BODIES);
        		sc.setPhantomClass();
        	}
        
		// We explicitly select the packs we want to run for performance
        // reasons. Do not re-run the callgraph algorithm if the host
        // application already provides us with a CG.
		if (config.getCallgraphAlgorithm() != CallgraphAlgorithm.OnDemand
				&& !Scene.v().hasCallGraph()) {
	        PackManager.v().getPack("wjpp").apply();
	        PackManager.v().getPack("cg").apply();
		}
		
		// Run the preprocessors
        for (PreAnalysisHandler tr : preProcessors)
            tr.onAfterCallgraphConstruction();
	}
	
    public void setConfig(InfoflowConfiguration config) {
    	this.config = config;
    }
    
	public void setTaintWrapper(ITaintPropagationWrapper wrapper) {
		taintWrapper = wrapper;
	}
	
	public void setSootConfig(IInfoflowConfig config) {
		sootConfig = config;
	}
	
	public void setIPCManager(IIPCManager ipcManager) {
	    this.ipcManager = ipcManager;
	}

}

