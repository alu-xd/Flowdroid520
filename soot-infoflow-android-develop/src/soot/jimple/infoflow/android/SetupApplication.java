/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.android;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;

import javax.activation.UnsupportedDataTypeException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.xml.sax.SAXException;
import org.xmlpull.v1.XmlPullParserException;

import soot.Main;
import soot.PackManager;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.Stmt;
import soot.jimple.infoflow.AbstractInfoflow;
import soot.jimple.infoflow.Infoflow;
import soot.jimple.infoflow.InfoflowforScan;
import soot.jimple.infoflow.android.ModeHandle.ModeHandle;
import soot.jimple.infoflow.android.callbacks.AbstractCallbackAnalyzer;
import soot.jimple.infoflow.android.callbacks.DefaultCallbackAnalyzer;
import soot.jimple.infoflow.android.callbacks.FastCallbackAnalyzer;
import soot.jimple.infoflow.android.config.SootConfigForAndroid;
import soot.jimple.infoflow.android.data.AndroidMethod;
import soot.jimple.infoflow.android.data.parsers.PermissionMethodParser;
import soot.jimple.infoflow.android.manifest.ProcessManifest;
import soot.jimple.infoflow.android.resources.ARSCFileParser;
import soot.jimple.infoflow.android.resources.ARSCFileParser.AbstractResource;
import soot.jimple.infoflow.android.resources.ARSCFileParser.StringResource;
import soot.jimple.infoflow.android.resources.LayoutControl;
import soot.jimple.infoflow.android.resources.LayoutFileParser;
import soot.jimple.infoflow.android.source.AccessPathBasedSourceSinkManager;
import soot.jimple.infoflow.android.source.parsers.xml.XMLSourceSinkParser;
import soot.jimple.infoflow.cfg.BiDirICFGFactory;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.data.SootMethodAndClass;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory;
import soot.jimple.infoflow.entryPointCreators.AndroidEntryPointCreator;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.rifl.RIFLSourceSinkDefinitionProvider;
import soot.jimple.infoflow.source.data.ISourceSinkDefinitionProvider;
import soot.jimple.infoflow.source.data.SourceSinkDefinition;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.options.Options;

public class SetupApplication {

	private final Logger logger = LoggerFactory.getLogger(getClass());

	private ISourceSinkDefinitionProvider sourceSinkProvider;
	//罗丹修改，去掉callbackMethods的final关键字
		private  Map<String, Set<SootMethodAndClass>> callbackMethods =
					new HashMap<String, Set<SootMethodAndClass>>(10000);

	private InfoflowAndroidConfiguration config = new InfoflowAndroidConfiguration();
	
	private Set<String> entrypoints = null;
	private Set<String> callbackClasses = null;

	private List<ARSCFileParser.ResPackage> resourcePackages = null;
	private String appPackageName = "";

	private final String androidJar;
	private final boolean forceAndroidJar;
	private final String apkFileLocation;
	private final String additionalClasspath;
	private ITaintPropagationWrapper taintWrapper;
	
	private AccessPathBasedSourceSinkManager sourceSinkManager = null;
	private AndroidEntryPointCreator entryPointCreator = null;

	private IInfoflowConfig sootConfig = new SootConfigForAndroid();
	private BiDirICFGFactory cfgFactory = null;

	private IIPCManager ipcManager = null;
	
	private long maxMemoryConsumption = -1;
	
	private Set<Stmt> collectedSources = null;
	private Set<Stmt> collectedSinks = null;

	private String callbackFile = "AndroidCallbacks.txt"; 
	
	/**
	 * Creates a new instance of the {@link SetupApplication} class
	 * 
	 * @param androidJar
	 *            The path to the Android SDK's "platforms" directory if Soot shall automatically select the JAR file to
	 *            be used or the path to a single JAR file to force one.
	 * @param apkFileLocation
	 *            The path to the APK file to be analyzed
	 */
	public SetupApplication(String androidJar, String apkFileLocation) {
		this(androidJar, apkFileLocation, "", null);
	}

	/**
	 * Creates a new instance of the {@link SetupApplication} class
	 * 
	 * @param androidJar
	 *            The path to the Android SDK's "platforms" directory if
	 *            Soot shall automatically select the JAR file to
	 *            be used or the path to a single JAR file to force one.
	 * @param apkFileLocation
	 *            The path to the APK file to be analyzed
	 * @param ipcManager
	 *            The IPC manager to use for modelling inter-component and inter-application data flows
	 */
	public SetupApplication(String androidJar, String apkFileLocation,
			IIPCManager ipcManager) {
		this(androidJar, apkFileLocation, "", ipcManager);
	}
	
	/**
	 * Creates a new instance of the {@link SetupApplication} class
	 * 
	 * @param androidJar
	 *            The path to the Android SDK's "platforms" directory if
	 *            Soot shall automatically select the JAR file to
	 *            be used or the path to a single JAR file to force one.
	 * @param apkFileLocation
	 *            The path to the APK file to be analyzed
	 * @param ipcManager
	 *            The IPC manager to use for modelling inter-component and inter-application data flows
	 */
	public SetupApplication(String androidJar, String apkFileLocation,
			String additionalClasspath,
			IIPCManager ipcManager) {
		File f = new File(androidJar);
		this.forceAndroidJar = f.isFile();

		this.androidJar = androidJar;
		this.apkFileLocation = apkFileLocation;

		this.ipcManager = ipcManager;
		this.additionalClasspath = additionalClasspath;
	}
	
	/**
	 * Gets the set of sinks loaded into FlowDroid These are the sinks as
	 * they are defined through the SourceSinkManager.
	 * 
	 * @return The set of sinks loaded into FlowDroid
	 */
	public Set<SourceSinkDefinition> getSinks() {
		return this.sourceSinkProvider == null ? null
				: this.sourceSinkProvider.getSinks();
	}
	
	/**
	 * Gets the concrete instances of sinks that have been collected inside
	 * the app. This method returns null if source and sink logging has not
	 * been enabled (see InfoflowConfiguration.setLogSourcesAndSinks()).
	 * @return The set of concrete sink instances in the app
	 */
	public Set<Stmt> getCollectedSinks() {
		return collectedSinks;
	}

	/**
	 * Prints the list of sinks registered with FlowDroud to stdout
	 */
	public void printSinks() {
		if (this.sourceSinkProvider == null) {
			System.err.println("Sinks not calculated yet");
			return;
		}
		System.out.println("Sinks:");
		for (SourceSinkDefinition am : getSinks()) {
			System.out.println(am.toString());
		}
		System.out.println("End of Sinks");
	}

	/**
	 * Gets the set of sources loaded into FlowDroid. These are the sources as
	 * they are defined through the SourceSinkManager.
	 * 
	 * @return The set of sources loaded into FlowDroid
	 */
	public Set<SourceSinkDefinition> getSources() {
		return this.sourceSinkProvider == null ? null
				: this.sourceSinkProvider.getSources();
	}
	
	/**
	 * Gets the concrete instances of sources that have been collected inside
	 * the app. This method returns null if source and sink logging has not
	 * been enabled (see InfoflowConfiguration.setLogSourcesAndSinks()).
	 * @return The set of concrete source instances in the app
	 */
	public Set<Stmt> getCollectedSources() {
		return collectedSources;
	}

	/**
	 * Prints the list of sources registered with FlowDroud to stdout
	 */
	public void printSources() {
		if (this.sourceSinkProvider == null) {
			System.err.println("Sources not calculated yet");
			return;
		}
		System.out.println("Sources:");
		for (SourceSinkDefinition am : getSources()) {
			System.out.println(am.toString());
		}
		System.out.println("End of Sources");
	}

	/**
	 * Gets the set of classes containing entry point methods for the lifecycle
	 * 
	 * @return The set of classes containing entry point methods for the lifecycle
	 */
	public Set<String> getEntrypointClasses() {
		return entrypoints;
	}

	/**
	 * Prints list of classes containing entry points to stdout
	 */
	public void printEntrypoints() {
		if (this.entrypoints == null)
			System.out.println("Entry points not initialized");
		else {
			System.out.println("Classes containing entry points:");
			for (String className : entrypoints)
				System.out.println("\t" + className);
			System.out.println("End of Entrypoints");
		}
	}

	/**
	 * Sets the class names of callbacks.
	 *  If this value is null, it automatically loads the names from AndroidCallbacks.txt as the default behavior.
	 * @param callbackClasses
	 * 	        The class names of callbacks or null to use the default file.
	 */
	public void setCallbackClasses(Set<String> callbackClasses) {
		this.callbackClasses = callbackClasses;
	}

	public Set<String> getCallbackClasses() {
		return callbackClasses;
	}

	/**
	 * Sets the taint wrapper to be used for propagating taints over unknown (library) callees. If this value is null,
	 * no taint wrapping is used.
	 * 
	 * @param taintWrapper
	 *            The taint wrapper to use or null to disable taint wrapping
	 */
	public void setTaintWrapper(ITaintPropagationWrapper taintWrapper) {
		this.taintWrapper = taintWrapper;
	}

	/**
	 * Gets the taint wrapper to be used for propagating taints over unknown (library) callees. If this value is null,
	 * no taint wrapping is used.
	 * 
	 * @return The taint wrapper to use or null if taint wrapping is disabled
	 */
	public ITaintPropagationWrapper getTaintWrapper() {
		return this.taintWrapper;
	}

	/**
	 * Calculates the sets of sources, sinks, entry points, and callbacks methods for the given APK file.
	 * 
	 * @param sources
	 *            The methods that shall be considered as sources
	 * @param sinks
	 *            The methods that shall be considered as sinks
	 * @throws IOException
	 *             Thrown if the given source/sink file could not be read.
	 * @throws XmlPullParserException
	 *             Thrown if the Android manifest file could not be read.
	 */
	public void calculateSourcesSinksEntrypoints(Set<AndroidMethod> sources,
			Set<AndroidMethod> sinks) throws IOException, XmlPullParserException {
		final Set<SourceSinkDefinition> sourceDefs = new HashSet<>(sources.size());
		final Set<SourceSinkDefinition> sinkDefs = new HashSet<>(sinks.size());
		
		for (AndroidMethod am : sources)
			sourceDefs.add(new SourceSinkDefinition(am));
		for (AndroidMethod am : sinks)
			sinkDefs.add(new SourceSinkDefinition(am));
		
		ISourceSinkDefinitionProvider parser = new ISourceSinkDefinitionProvider() {
			
			@Override
			public Set<SourceSinkDefinition> getSources() {
				return sourceDefs;
			}
			
			@Override
			public Set<SourceSinkDefinition> getSinks() {
				return sinkDefs;
			}

			@Override
			public Set<SourceSinkDefinition> getAllMethods() {
				Set<SourceSinkDefinition> sourcesSinks = new HashSet<>(sourceDefs.size()
						+ sinkDefs.size());
				sourcesSinks.addAll(sourceDefs);
				sourcesSinks.addAll(sinkDefs);
				return sourcesSinks;
			}
			
		};
		
		calculateSourcesSinksEntrypoints(parser);
	}
	
	/**
	 * Calculates the sets of sources, sinks, entry points, and callback methods
	 * for the given APK file.
	 * 
	 * @param sourceSinkFile
	 *            The full path and file name of the file containing the sources and sinks
	 * @throws IOException
	 *             Thrown if the given source/sink file could not be read.
	 * @throws XmlPullParserException
	 *             Thrown if the Android manifest file could not be read.
	 */
	public void calculateSourcesSinksEntrypoints(String sourceSinkFile)
			throws IOException, XmlPullParserException {
		ISourceSinkDefinitionProvider parser = null;
		
		String fileExtension = sourceSinkFile.substring(sourceSinkFile.lastIndexOf("."));
		fileExtension = fileExtension.toLowerCase();
		
		try {
			if (fileExtension.equals(".xml"))
				parser = XMLSourceSinkParser.fromFile(sourceSinkFile);
			else if (fileExtension.equals(".txt"))
				parser = PermissionMethodParser.fromFile(sourceSinkFile);
			else if (fileExtension.equals(".rifl"))
				parser = new RIFLSourceSinkDefinitionProvider(sourceSinkFile);
			else
				throw new UnsupportedDataTypeException("The Inputfile isn't a .txt or .xml file.");
			
			calculateSourcesSinksEntrypoints(parser);
		}
		catch (SAXException ex) {
			throw new IOException("Could not read XML file", ex);
		}
	}

	/**
	 * Calculates the sets of sources, sinks, entry points, and callbacks methods for the given APK file.
	 * 
	 * @param sourcesAndSinks
	 *            A provider from which the analysis can obtain the list of
	 *            sources and sinks
	 * @throws IOException
	 *             Thrown if the given source/sink file could not be read.
	 * @throws XmlPullParserException
	 *             Thrown if the Android manifest file could not be read.
	 */
	public void calculateSourcesSinksEntrypoints(ISourceSinkDefinitionProvider sourcesAndSinks)
			throws IOException, XmlPullParserException {
		// To look for callbacks, we need to start somewhere. We use the Android
		// lifecycle methods for this purpose.
		this.sourceSinkProvider = sourcesAndSinks;
		ProcessManifest processMan = new ProcessManifest(apkFileLocation);
		this.appPackageName = processMan.getPackageName();
		
		
		//原来的代码：
				// this.entrypoints = processMan.getEntryPointClasses();
				//罗丹修改开始：
		if(!this.config.getAndroidconfig().getTestOnebyoneentrypoints().equals(""))
		{
			this.entrypoints= new HashSet<String>();
			entrypoints.add(this.currententrypoints);
		}
		else if( ! this.config.getAndroidconfig().isUseEntrypointsconfig() && this.config.getAndroidconfig().isPrintEntryAndCallbacksConfig())
		{
			this.entrypointsset = processMan.getEntryPointClassesset();
			entrypoints= new HashSet<String>();
			for(int i=0;i<entrypointsset.length;i++)
			{
				entrypoints.addAll(entrypointsset[i]);
			}
		}
		else if( ! this.config.getAndroidconfig().isUseEntrypointsconfig())
		    this.entrypoints = processMan.getEntryPointClasses(this.config.getAndroidconfig().getUseEntrypointskind());
		else
		{
			//记得在读取时，设置entrypoints变量的值
			this.entrypoints= new HashSet<String>();
			if( !ModeHandle.readentrypoints("entrypointscollected.txt",this.entrypoints,config.getAndroidconfig().getUseEntrypointskind()))
			{
				System.out.println("读取配置文件entrypointscollected.txt有错");
				return;
			}
		}
	   //罗丹修改结束

		// Parse the resource file
		long beforeARSC = System.nanoTime();
		ARSCFileParser resParser = new ARSCFileParser();
		resParser.parse(apkFileLocation);
		logger.info("ARSC file parsing took " + (System.nanoTime() - beforeARSC) / 1E9 + " seconds");
		this.resourcePackages = resParser.getPackages();

		// Add the callback methods
		LayoutFileParser lfp = null;
		if (config.getEnableCallbacks()) {
			if (callbackClasses != null && callbackClasses.isEmpty()) {
				logger.warn("Callback definition file is empty, disabling callbacks");
			}
			else {
				lfp = new LayoutFileParser(this.appPackageName, resParser);
				switch (config.getCallbackAnalyzer()) {
				case Fast:
					calculateCallbackMethodsFast(resParser, lfp);
					break;
				case Default:
				{
					calculateCallbackMethods(resParser, lfp);
					if( !this.config.getAndroidconfig().isUseCallbacksconfig())
					{	
						validateConfig();
					}
					//罗丹修改结束
				}
					break;
				default:
					throw new RuntimeException("Unknown callback analyzer");
				}
				
				// Some informational output
				//System.out.println("Found " + lfp.getUserControls() + " layout controls");
			}
		}
		
		System.out.println("Entry point calculation done.");

		// Clean up everything we no longer need
		soot.G.reset();

		// Create the SourceSinkManager
		{
			Set<SootMethodAndClass> callbacks = new HashSet<>();
			for (Set<SootMethodAndClass> methods : this.callbackMethods.values())
				callbacks.addAll(methods);

			sourceSinkManager = new AccessPathBasedSourceSinkManager(
					this.sourceSinkProvider.getSources(),
					this.sourceSinkProvider.getSinks(),
					callbacks,
					config.getLayoutMatchingMode(),
					lfp == null ? null : lfp.getUserControlsByID());

			sourceSinkManager.setAppPackageName(this.appPackageName);
			sourceSinkManager.setResourcePackages(this.resourcePackages);
			sourceSinkManager.setEnableCallbackSources(this.config.getEnableCallbackSources());
		}

		entryPointCreator = createEntryPointCreator();
	}

	/**
	 * Adds a method to the set of callback method
	 * 
	 * @param layoutClass
	 *            The layout class for which to register the callback
	 * @param callbackMethod
	 *            The callback method to register
	 */
	private void addCallbackMethod(String layoutClass, AndroidMethod callbackMethod) {
		Set<SootMethodAndClass> methods = this.callbackMethods.get(layoutClass);
		if (methods == null) {
			methods = new HashSet<SootMethodAndClass>();
			this.callbackMethods.put(layoutClass, methods);
		}
		methods.add(new AndroidMethod(callbackMethod));
	}

	/**
	 * Calculates the set of callback methods declared in the XML resource files or the app's source code
	 * 
	 * @param resParser
	 *            The binary resource parser containing the app resources
	 * @param lfp
	 *            The layout file parser to be used for analyzing UI controls
	 * @throws IOException
	 *             Thrown if a required configuration cannot be read
	 */
	private void calculateCallbackMethods(ARSCFileParser resParser, LayoutFileParser lfp) throws IOException {
		AbstractCallbackAnalyzer jimpleClass = null;

		boolean hasChanged = true;
		while (hasChanged) {
			hasChanged = false;

			// Create the new iteration of the main method
			soot.G.reset();
			initializeSoot(true);
			createMainMethod();

			if (jimpleClass == null) {
				// Collect the callback interfaces implemented in the app's
				// source code
				jimpleClass = callbackClasses == null
						? new DefaultCallbackAnalyzer(config, entrypoints, callbackFile)
						: new DefaultCallbackAnalyzer(config, entrypoints, callbackClasses);
				jimpleClass.collectCallbackMethods();

				// Find the user-defined sources in the layout XML files. This
				// only needs to be done once, but is a Soot phase.
				lfp.parseLayoutFile(apkFileLocation);
			} else
				jimpleClass.collectCallbackMethodsIncremental();

			// Run the soot-based operations
			PackManager.v().getPack("wjpp").apply();
			PackManager.v().getPack("cg").apply();
			PackManager.v().getPack("wjtp").apply();

			// Collect the results of the soot-based phases
			for (Entry<String, Set<SootMethodAndClass>> entry : jimpleClass.getCallbackMethods().entrySet()) {
				Set<SootMethodAndClass> curCallbacks = this.callbackMethods.get(entry.getKey());
				if (curCallbacks != null) {
					if (curCallbacks.addAll(entry.getValue()))
						hasChanged = true;
				} else {
					this.callbackMethods.put(entry.getKey(), new HashSet<>(entry.getValue()));
					hasChanged = true;
				}
			}
			
			/*原来的代码：
			 * if (entrypoints.addAll(jimpleClass.getDynamicManifestComponents()))
				hasChanged = true;*/
			if(this.config.getAndroidconfig().getUseEntrypointskind().indexOf("B")>-1)
			{   
				if (entrypoints.addAll(jimpleClass.getDynamicManifestComponents()))
				     hasChanged = true;
				if(this.config.getAndroidconfig().isPrintEntryAndCallbacksConfig())
				{
					this.entrypointsset[1].addAll( jimpleClass.getDynamicManifestComponents() ) ;
				}
			}
			//罗丹修改结束
		}

		// Collect the XML-based callback methods
		collectXmlBasedCallbackMethods(resParser, lfp, jimpleClass);
	}

	/**
	 * Collects the XML-based callback methods, e.g., Button.onClick() declared
	 * in layout XML files
	 * @param resParser The ARSC resource parser
	 * @param lfp The layout file parser
	 * @param jimpleClass The analysis class that gives us a mapping between
	 * layout IDs and components
	 */
	private void collectXmlBasedCallbackMethods(ARSCFileParser resParser,
			LayoutFileParser lfp, AbstractCallbackAnalyzer jimpleClass) {
		// Collect the XML-based callback methods
		for (Entry<String, Set<Integer>> lcentry : jimpleClass.getLayoutClasses().entrySet()) {
			final SootClass callbackClass = Scene.v().getSootClass(lcentry.getKey());

			for (Integer classId : lcentry.getValue()) {
				AbstractResource resource = resParser.findResource(classId);
				if (resource instanceof StringResource) {
					final String layoutFileName = ((StringResource) resource).getValue();

					// Add the callback methods for the given class
					Set<String> callbackMethods = lfp.getCallbackMethods().get(layoutFileName);
					if (callbackMethods != null) {
						for (String methodName : callbackMethods) {
							final String subSig = "void " + methodName + "(android.view.View)";

							// The callback may be declared directly in the
							// class
							// or in one of the superclasses
							SootClass currentClass = callbackClass;
							while (true) {
								SootMethod callbackMethod = currentClass.getMethodUnsafe(subSig);
								if (callbackMethod != null) {
									addCallbackMethod(callbackClass.getName(), new AndroidMethod(callbackMethod));
									break;
								}
								if (!currentClass.hasSuperclass()) {
									System.err.println("Callback method " + methodName + " not found in class "
											+ callbackClass.getName());
									break;
								}
								currentClass = currentClass.getSuperclass();
							}
						}
					}

					// For user-defined views, we need to emulate their
					// callbacks
					Set<LayoutControl> controls = lfp.getUserControls().get(layoutFileName);
					if (controls != null)
						for (LayoutControl lc : controls)
							registerCallbackMethodsForView(callbackClass, lc);
				} else
					System.err.println("Unexpected resource type for layout class");
			}
		}
		
		// Add the callback methods as sources and sinks
		{
			Set<SootMethodAndClass> callbacksPlain = new HashSet<SootMethodAndClass>();
			for (Set<SootMethodAndClass> set : this.callbackMethods.values())
				callbacksPlain.addAll(set);
			System.out.println("Found " + callbacksPlain.size() + " callback methods for "
					+ this.callbackMethods.size() + " components");
		}
	}
	
	/**
	 * Calculates the set of callback methods declared in the XML resource
	 * files or the app's source code. This method prefers performance over
	 * precision and scans the code including unreachable methods. 
	 * 
	 * @param resParser
	 *            The binary resource parser containing the app resources
	 * @param lfp
	 *            The layout file parser to be used for analyzing UI controls
	 * @throws IOException
	 *             Thrown if a required configuration cannot be read
	 */
	private void calculateCallbackMethodsFast(ARSCFileParser resParser,
			LayoutFileParser lfp) throws IOException {
		// We need a running Soot instance
		soot.G.reset();
		initializeSoot(false);
		
		// Collect the callback interfaces implemented in the app's
		// source code
		AbstractCallbackAnalyzer jimpleClass = callbackClasses == null
				? new FastCallbackAnalyzer(config, entrypoints, callbackFile)
				: new FastCallbackAnalyzer(config, entrypoints, callbackClasses);
		jimpleClass.collectCallbackMethods();
		
		// Collect the results
		Set<SootMethodAndClass> callbacks = jimpleClass.getCallbackMethods().get("");
		if (callbacks != null) {
			for (String componentName : this.entrypoints)
				callbackMethods.put(componentName, callbacks);
		}
		
		// Find the user-defined sources in the layout XML files. This
		// only needs to be done once, but is a Soot phase.
		lfp.parseLayoutFileDirect(apkFileLocation);
		
		// Collect the XML-based callback methods
		collectXmlBasedCallbackMethods(resParser, lfp, jimpleClass);
	}
	
	/**
	 * Registers the callback methods in the given layout control so that they
	 * are included in the dummy main method
	 * @param callbackClass The class with which to associate the layout
	 * callbacks
	 * @param lc The layout control whose callbacks are to be associated with
	 * the given class
	 */
	private void registerCallbackMethodsForView(SootClass callbackClass, LayoutControl lc) {
		// Ignore system classes
		if (callbackClass.getName().startsWith("android."))
			return;
		if (lc.getViewClass().getName().startsWith("android."))
			return;
		
		// Check whether the current class is actually a view
		{
			SootClass sc = lc.getViewClass();
			boolean isView = false;
			while (sc.hasSuperclass()) {
				if (sc.getName().equals("android.view.View")) {
					isView = true;
					break;
				}
				sc = sc.getSuperclass();
			}
			if (!isView)
				return;
		}

		// There are also some classes that implement interesting callback
		// methods.
		// We model this as follows: Whenever the user overwrites a method in an
		// Android OS class, we treat it as a potential callback.
		SootClass sc = lc.getViewClass();
		Set<String> systemMethods = new HashSet<String>(10000);
		for (SootClass parentClass : Scene.v().getActiveHierarchy().getSuperclassesOf(sc)) {
			if (parentClass.getName().startsWith("android."))
				for (SootMethod sm : parentClass.getMethods())
					if (!sm.isConstructor())
						systemMethods.add(sm.getSubSignature());
		}

		// Scan for methods that overwrite parent class methods
		for (SootMethod sm : sc.getMethods())
			if (!sm.isConstructor())
				if (systemMethods.contains(sm.getSubSignature()))
					// This is a real callback method
					addCallbackMethod(callbackClass.getName(), new AndroidMethod(sm));
	}

	/**
	 * Creates the main method based on the current callback information, injects it into the Soot scene.
	 */
	private void createMainMethod() {
		// Always update the entry point creator to reflect the newest set
		// of callback methods
		SootMethod entryPoint = createEntryPointCreator().createDummyMain();
		Scene.v().setEntryPoints(Collections.singletonList(entryPoint));
		if (Scene.v().containsClass(entryPoint.getDeclaringClass().getName()))
			Scene.v().removeClass(entryPoint.getDeclaringClass());
		Scene.v().addClass(entryPoint.getDeclaringClass());
		
		// addClass() declares the given class as a library class. We need to
		// fix this.
		entryPoint.getDeclaringClass().setApplicationClass();
	}

	/**
	 * Gets the source/sink manager constructed for FlowDroid. Make sure to call calculateSourcesSinksEntryPoints()
	 * first, or you will get a null result.
	 * 
	 * @return FlowDroid's source/sink manager
	 */
	public AccessPathBasedSourceSinkManager getSourceSinkManager() {
		return sourceSinkManager;
	}
	
	/**
	 * Builds the classpath for this analysis
	 * @return The classpath to be used for the taint analysis
	 */
	private String getClasspath() {
		String classpath = forceAndroidJar ? androidJar
				: Scene.v().getAndroidJarPath(androidJar, apkFileLocation);
		if (this.additionalClasspath != null && !this.additionalClasspath.isEmpty())
			classpath += File.pathSeparator + this.additionalClasspath;
		logger.debug("soot classpath: " + classpath);
		return classpath;
	}

	/**
	 * Initializes soot for running the soot-based phases of the application metadata analysis
	 * @param constructCallgraph True if a callgraph shall be constructed, otherwise false
	 */
	private void initializeSoot(boolean constructCallgraph) {
		Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_output_format(Options.output_format_none);
		Options.v().set_whole_program(constructCallgraph);
		Options.v().set_process_dir(Collections.singletonList(apkFileLocation));
		if (forceAndroidJar)
			Options.v().set_force_android_jar(androidJar);
		else
			Options.v().set_android_jars(androidJar);
		Options.v().set_src_prec(Options.src_prec_apk_class_jimple);
		Options.v().set_keep_line_number(false);
		Options.v().set_keep_offset(false);
		
		// Set the Soot configuration options. Note that this will needs to be
		// done before we compute the classpath.
		if (sootConfig != null)
			sootConfig.setSootOptions(Options.v());
		
		Options.v().set_soot_classpath(getClasspath());
		Main.v().autoSetOptions();
		
		// Configure the callgraph algorithm
		if (constructCallgraph) {
			switch (config.getCallgraphAlgorithm()) {
			case AutomaticSelection:
			case SPARK:
				Options.v().setPhaseOption("cg.spark", "on");
				break;
			case GEOM:
				Options.v().setPhaseOption("cg.spark", "on");
				AbstractInfoflow.setGeomPtaSpecificOptions();
				break;
			case CHA:
				Options.v().setPhaseOption("cg.cha", "on");
				break;
			case RTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "rta:true");
				Options.v().setPhaseOption("cg.spark", "on-fly-cg:false");
				break;
			case VTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "vta:true");
				break;
			default:
				throw new RuntimeException("Invalid callgraph algorithm");
			}
		}

		// Load whetever we need
		Scene.v().loadNecessaryClasses();
	}

	/**
	 * Runs the data flow analysis
	 * 
	 * @return The results of the data flow analysis
	 */
	public InfoflowResults runInfoflow() {
		return runInfoflow(null);
	}

	/**
	 * Runs the data flow analysis. Make sure to populate the sets of sources, sinks, and entry points first.
	 * 
	 * @param onResultsAvailable
	 *            The callback to be invoked when data flow results are available
	 * @return The results of the data flow analysis
	 */
	public InfoflowResults runInfoflow(ResultsAvailableHandler onResultsAvailable) {
		if (this.sourceSinkProvider == null)
			throw new RuntimeException("Sources and/or sinks not calculated yet");

		System.out.println("Running data flow analysis on " + apkFileLocation + " with " + getSources().size()
				+ " sources and " + getSinks().size() + " sinks...");
		Infoflow info;
		if (cfgFactory == null)
			info = new Infoflow(androidJar, forceAndroidJar, null,
					new DefaultPathBuilderFactory(config.getPathBuilder(),
							config.getComputeResultPaths()));
		else
			info = new Infoflow(androidJar, forceAndroidJar, cfgFactory,
					new DefaultPathBuilderFactory(config.getPathBuilder(),
							config.getComputeResultPaths()));

		final String path;
		if (forceAndroidJar)
			path = androidJar;
		else
			path = Scene.v().getAndroidJarPath(androidJar, apkFileLocation);

		info.setTaintWrapper(taintWrapper);
		if (onResultsAvailable != null)
			info.addResultsAvailableHandler(onResultsAvailable);

		System.out.println("Starting infoflow computation...");
		info.setConfig(config);
		info.setSootConfig(sootConfig);
		
		if (null != ipcManager) {
			info.setIPCManager(ipcManager);
		}

		
		//罗丹添加判断
		if(this.config.getAndroidconfig().isPrintEntryAndCallbacksConfig())
		{
			printConfig();
		}
				
		info.computeInfoflow(apkFileLocation, path, entryPointCreator, sourceSinkManager);
		this.maxMemoryConsumption = info.getMaxMemoryConsumption();
		this.collectedSources = info.getCollectedSources();
		this.collectedSinks = info.getCollectedSinks();

		return info.getResults();
	}

	private AndroidEntryPointCreator createEntryPointCreator() {
		AndroidEntryPointCreator entryPointCreator = new AndroidEntryPointCreator(new ArrayList<String>(
				this.entrypoints));
		
		//罗丹添加
		entryPointCreator.setPrintDummymain(config.getAndroidconfig().isPrintDummymain());
		Map<String, List<String>> callbackMethodSigs = new HashMap<String, List<String>>();
		for (String className : this.callbackMethods.keySet()) {
			List<String> methodSigs = new ArrayList<String>();
			callbackMethodSigs.put(className, methodSigs);
			for (SootMethodAndClass am : this.callbackMethods.get(className))
				methodSigs.add(am.getSignature());
		}
		entryPointCreator.setCallbackFunctions(callbackMethodSigs);
		return entryPointCreator;
	}

	/**
	 * Gets the entry point creator used for generating the dummy main method emulating the Android lifecycle and the
	 * callbacks. Make sure to call calculateSourcesSinksEntryPoints() first, or you will get a null result.
	 * 
	 * @return The entry point creator
	 */
	public AndroidEntryPointCreator getEntryPointCreator() {
		return entryPointCreator;
	}
	
	/**
	 * Gets the extra Soot configuration options to be used when running the analysis
	 * 
	 * @return The extra Soot configuration options to be used when running the analysis, null if the defaults shall be
	 *         used
	 */
	public IInfoflowConfig getSootConfig() {
		return this.sootConfig;
	}

	/**
	 * Sets the extra Soot configuration options to be used when running the analysis
	 * 
	 * @param config
	 *            The extra Soot configuration options to be used when running the analysis, null if the defaults shall
	 *            be used
	 */
	public void setSootConfig(IInfoflowConfig config) {
		this.sootConfig = config;
	}

	/**
	 * Sets the factory class to be used for constructing interprocedural control flow graphs
	 * 
	 * @param factory
	 *            The factory to be used. If null is passed, the default factory is used.
	 */
	public void setIcfgFactory(BiDirICFGFactory factory) {
		this.cfgFactory = factory;
	}
	
	/**
	 * Gets the maximum memory consumption during the last analysis run
	 * 
	 * @return The maximum memory consumption during the last analysis run if available, otherwise -1
	 */
	public long getMaxMemoryConsumption() {
		return this.maxMemoryConsumption;
	}
	
	/**
	 * Gets the data flow configuration
	 * @return The current data flow configuration
	 */
	public InfoflowAndroidConfiguration getConfig() {
		return this.config;
	}
	
	/**
	 * Sets the data flow configuration
	 * @param config The new data flow configuration
	 */
	public void setConfig(InfoflowAndroidConfiguration config) {
		this.config = config;
	}
	
	public void setCallbackFile(String callbackFile) {
		this.callbackFile = callbackFile;
	}
	
	
	
	
	//罗丹添加
	
	private  Set<String>[] entrypointsset;
	private String currententrypoints;
	private LayoutFileParser lfp;
//	private AnalyzeJimpleClass jimpleClass = null;
//罗丹添加结束
	
	
	
//罗丹添加

	
	
	
	public void printConfig()
	{
		printEntryconfig();
		printCallbackconfig();
		
	}
	public void printEntryconfig()
	{
		//输出默认文件名：entrypointscollected.txt
		if(this.config.getAndroidconfig().isUseEntrypointsconfig())
			return;
				try
				{
					File entrypointfile = new File("entrypointscollected.txt");
					if(entrypointfile.exists() )
					{
						//删除文件
						entrypointfile.delete();
						System.out.println("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
					}

					 BufferedWriter entrypointsbw = new BufferedWriter(new FileWriter(entrypointfile));
					 String entrypointskind[]=new String[5];
					 entrypointskind[0]="Activity";
					 entrypointskind[1]="Broadcast receiver";
					 entrypointskind[2]="Content providers";
					 entrypointskind[3]="Services";
					 entrypointskind[4]="P(Application)";
					
					 for(int i=0;i<entrypointsset.length;i++)
					{
						if(entrypointsset[i].isEmpty())
							continue;
						entrypointsbw.write("--"+entrypointskind[i]);entrypointsbw.newLine();
						for(String entrypoints:entrypointsset[i])
						{
							entrypointsbw.write(entrypoints);entrypointsbw.newLine();
						}
						entrypointsbw.newLine();entrypointsbw.newLine();entrypointsbw.newLine();
					}
					entrypointsbw.close();
					
				
				} catch (IOException e)
				{ 
		    	   System.out.printf("创建/删除/写文件出错 \n ");
		    	   e.printStackTrace();
		    	 }
				
	}
	public void printCallbackconfig()
	{
				try
				{
					
					File callbackfile = new File("callbackscollected.txt");
					File callbackfile2 = new File("callbackscollected2.txt");
					
					if(callbackfile.exists())
					{
						callbackfile.delete();
					}
					if(callbackfile2.exists())
					{
						callbackfile2.delete();
					}

					 BufferedWriter callbacksbw = new BufferedWriter(new FileWriter(callbackfile));
					 BufferedWriter callbacksbw2 = new BufferedWriter(new FileWriter(callbackfile2));

					for(String entry :this.callbackMethods.keySet())
					{
						callbacksbw.write("--"+entry);
						callbacksbw.newLine();
						
						callbacksbw2.write("--"+entry);
						callbacksbw2.newLine();
						
						for(SootMethodAndClass method:this.callbackMethods.get(entry))
						{
							callbacksbw.write(method.getMethodName());callbacksbw.newLine();
							callbacksbw2.write(method.getSignature());callbacksbw2.newLine();
						}
						callbacksbw.newLine();callbacksbw.newLine();callbacksbw.newLine();
						callbacksbw2.newLine();callbacksbw2.newLine();callbacksbw2.newLine();
					}
					callbacksbw.close();
					callbacksbw2.close();
				} catch (IOException e)
				{ 
		    	   System.out.printf("创建/删除/写文件出错 \n ");
		    	   e.printStackTrace();
		    	 }
				
	}
	
	public boolean validateConfig()
	{
		
			
		//读取AndroidCallbacks文件，读取回调配置文件，初始化内容
		int sum=0;
        Map<String, Set<String>> tempString=Collections.emptyMap(); 
        
        System.out.println("Using callbackscollected2.txt file to trim some callbacks");
		try{
				if(entrypoints.isEmpty())
				{
					System.out.println("请先初始化好入口类信息，是不是使用了useEntrypointsconfig参数，但是"
							+ "配置文件中没有内容！");
					return false;
				}
				
				
				File file=new File("callbackscollected2.txt");
		        if (!file.exists()) 
		        {
		               System.out.println("Callback definition file not found");
		               return false;
		        }
		        BufferedReader rdr = new BufferedReader(new FileReader(file));
		        String line;
		        String classname="";
		        tempString=new HashMap<String, Set<String>>(1000);
		        while ((line = rdr.readLine()) != null)
		        {
		        	line=line.trim();
		        	if(line.startsWith("--"))
		        		classname=line.substring(2);
		        	else if(!line.isEmpty())
		        	{    
		        		if(!entrypoints.contains(classname))
		        		    continue;

		        		else
		        		{
		        			
		        			if(tempString.containsKey(classname))
		        				tempString.get(classname).add(line);
		        			else{
		        				Set temp=new HashSet<String>();
		        				temp.add(line);
		        				tempString.put(classname, temp);
		        			}
		        		}
		        	}
		        }
				rdr.close();
		}catch(IOException e)
		{
			System.out.println("回调配置文件读写出错！");
			e.printStackTrace();
					
		}
		
		
		
		//去除不要的
		Map<String, Set<SootMethodAndClass>> tempcallbackMethods =new HashMap<String, Set<SootMethodAndClass>>(1000);
		SootMethodAndClass now;
		String key,sig;
		
		Iterator it=this.callbackMethods.entrySet().iterator();
		while(it.hasNext())
		{
			Map.Entry<String, Set<SootMethodAndClass>>entry=(Entry<String, Set<SootMethodAndClass>>) it.next();
			key=entry.getKey();
			if(tempString.containsKey(key ))
			{
				Iterator method=entry.getValue().iterator();
				while(method.hasNext())
				{
					now=(SootMethodAndClass) method.next();
					sig=now.getSignature();
					if(tempString.get(key).contains(sig))
					{
						if(tempcallbackMethods.containsKey(key) )
							tempcallbackMethods.get(key).add(now);
						else
						{
							Set<SootMethodAndClass> t=new HashSet<SootMethodAndClass>();
							t.add(now);
							tempcallbackMethods.put(key, t);
						}
					}
				}
				
				Set<SootMethodAndClass> t=tempcallbackMethods.get(key);
				if(t!=null)
				   sum=sum+ entry.getValue().size()  - t.size();
				else
					sum=sum+ entry.getValue().size();
			}
			else
				sum=sum+entry.getValue().size();
		}
		
		System.out.println("has trim "+ sum+ " callbacks");
		
		this.callbackMethods=null;
		
		this.callbackMethods=tempcallbackMethods;
		return true;
	}
	
	
	public void printCallbackMethods()
	{
		for (Set<SootMethodAndClass> set : this.callbackMethods.values())
		{
			Iterator<SootMethodAndClass> it=set.iterator();
			
			while(it.hasNext())
			{
				SootMethodAndClass  current=it.next();
				logger.warn("callbackMethods中含有"+current.getSignature());
			}
			
		}
	}
	
	
	
	public String getMethodclass(String methodsig)
	{
		String temp=methodsig;
		temp=temp.trim();
		
		String methodclass;
		int index=temp.indexOf(':');
		methodclass=temp.substring(1, index);
		methodclass=methodclass.trim();
		return methodclass;
	}
	public String getMethodsubsig(String methodsig)
	{
		String temp=methodsig;
		temp=temp.trim();
		String methodname;
		int index=temp.indexOf(':');
		methodname=temp.substring(index+1);
		methodname=methodname.trim();
		methodname=methodname.substring(0, methodname.length()-1);
		methodname=methodname.trim();
		//System.out.println(methodname);
		return methodname;
	}
	
	//只是初始化sourceSinkManager,xcallbacks模式下调用
	/*public void calculateSourcesSinksEntrypoints_version2(String sourceSinkFile) throws IOException, XmlPullParserException {
		ISourceSinkDefinitionProvider parser = null;

		String fileExtension = sourceSinkFile.substring(sourceSinkFile.lastIndexOf("."));
		fileExtension = fileExtension.toLowerCase();
		
		if (fileExtension.equals(".xml"))
			parser = XMLSourceSinkParser.fromFile(sourceSinkFile);
		else if(fileExtension.equals(".txt"))
			parser = PermissionMethodParser.fromFile(sourceSinkFile);
		else
			throw new UnsupportedDataTypeException("The Inputfile isn't a .txt or .xml file.");
		
		
		
		// To look for callbacks, we need to start somewhere. We use the Android
				// lifecycle methods for this purpose.
		this.sourceSinkProvider = parser;
		ProcessManifest processMan = new ProcessManifest(apkFileLocation);
		this.appPackageName = processMan.getPackageName();
		this.entrypoints = processMan.getEntryPointClasses();

		
		
		// Parse the resource file
		long beforeARSC = System.nanoTime();
		ARSCFileParser resParser = new ARSCFileParser();
		resParser.parse(apkFileLocation);
		logger.info("ARSC file parsing took " + (System.nanoTime() - beforeARSC) / 1E9 + " seconds");
		this.resourcePackages = resParser.getPackages();

		soot.G.reset();

		// Create the SourceSinkManager
		{
			Set<SootMethodAndClass> callbacks = new HashSet<>();
			for (Set<SootMethodAndClass> methods : this.callbackMethods.values())
				callbacks.addAll(methods);

			sourceSinkManager = new AccessPathBasedSourceSinkManager(
					this.sourceSinkProvider.getSources(),
					this.sourceSinkProvider.getSinks(),
					callbacks,
					config.getLayoutMatchingMode(),
					lfp == null ? null : lfp.getUserControlsByID());

			sourceSinkManager.setAppPackageName(this.appPackageName);
			sourceSinkManager.setResourcePackages(this.resourcePackages);
			sourceSinkManager.setEnableCallbackSources(this.config.getEnableCallbackSources());
		}

		entryPointCreator = createEntryPointCreator();
	}*/
	
	//罗丹添加函数，在GUI模式下调用的
	/*public void initSelfDefineConfigure(String sourceSinkFile) throws IOException, XmlPullParserException {
		ISourceSinkDefinitionProvider sourcesAndSinks = null;

		String fileExtension = sourceSinkFile.substring(sourceSinkFile.lastIndexOf("."));
		fileExtension = fileExtension.toLowerCase();
		
		if (fileExtension.equals(".xml"))
			sourcesAndSinks = XMLSourceSinkParser.fromFile(sourceSinkFile);
		else if(fileExtension.equals(".txt"))
			sourcesAndSinks = PermissionMethodParser.fromFile(sourceSinkFile);
		else
			throw new UnsupportedDataTypeException("The Inputfile isn't a .txt or .xml file.");
		
		this.sourceSinkProvider = sourcesAndSinks;
		
		//这个需要在
		this.appPackageName = ConfigureDataFromGUI.getAppPackageName();
		this.entrypoints= new HashSet<String>();
		for(int i=0;i<ConfigureDataFromGUI.getSelectEntrypoints().length ;i++)
		{
			entrypoints.addAll(ConfigureDataFromGUI.getSelectEntrypoints()[i]);
		}
		
		
	
		ARSCFileParser resParser = new ARSCFileParser();
		resParser.parse(apkFileLocation);
		this.resourcePackages = resParser.getPackages();

		// Add the callback methods
		LayoutFileParser lfp = null;
		if (config.getEnableCallbacks()) {
			lfp = new LayoutFileParser(this.appPackageName, resParser);
			this.callbackMethodSigs =ConfigureDataFromGUI.getSelectCallbacks();
			////////////////////////////////////////////////////
			
			findandsetSootMethodAndClass(resParser,lfp);

			////////////////////////////////
		}
		
        if(ConfigureDataFromGUI.isDEBUG())
        {
        	Iterator<String> it=entrypoints.iterator();
        	int i=0;
        	while(it.hasNext())
    		{
    			System.out.println("entrypoints "+i +" :"+it.next());
    			i++;
    		}
        	i=0;
        	for(String key:this.callbackMethodSigs.keySet())
        	{
        		//System.out.println(this.callbackMethodSigs.get(key).toString());
        		it=this.callbackMethodSigs.get(key).iterator();
        		while(it.hasNext())
        		{
        			System.out.println("callbacks "+i +" :"+it.next());
        			i++;
        		}
        	}
        	
        	
        }
		// Create the SourceSinkManager
		{
			Set<SootMethodAndClass> callbacks = new HashSet<>();
			for (Set<SootMethodAndClass> methods : this.callbackMethods.values())
				callbacks.addAll(methods);

			sourceSinkManager = new AccessPathBasedSourceSinkManager(
					this.sourceSinkProvider.getSources(),
					this.sourceSinkProvider.getSinks(),
					callbacks,
					config.getLayoutMatchingMode(),
					lfp == null ? null : lfp.getUserControlsByID());

			sourceSinkManager.setAppPackageName(this.appPackageName);
			sourceSinkManager.setResourcePackages(this.resourcePackages);
			sourceSinkManager.setEnableCallbackSources(this.config.getEnableCallbackSources());
		}

		entryPointCreator = createEntryPointCreator();
	}
*/			
	//罗丹添加，用来在justlooking模式下调用，只找回调，并返回新添加的broadcast
	public Set<String> calculateEntrypoints(String currententrypoints)
			throws IOException, XmlPullParserException {
		// To look for callbacks, we need to start somewhere. We use the Android
		// lifecycle methods for this purpose.
		
		if(currententrypoints.equals(""))
		{
			ProcessManifest processMan = new ProcessManifest(apkFileLocation);
			this.entrypoints = processMan.getEntryPointClasses();
		}
		else
		{
			this.entrypoints=new HashSet<String>();
			entrypoints.add(currententrypoints);
		}
	
		// Parse the resource file
		long beforeARSC = System.nanoTime();
		ARSCFileParser resParser = new ARSCFileParser();
		resParser.parse(apkFileLocation);
		logger.info("ARSC file parsing took " + (System.nanoTime() - beforeARSC) / 1E9 + " seconds");
		this.resourcePackages = resParser.getPackages();

		// Add the callback methods
		LayoutFileParser lfp = null;
		Set<String> newbroadcast=null;
		
		if(config.getEnableCallbacks()) {
			lfp = new LayoutFileParser(this.appPackageName, resParser);
			/*calculateCallbackMethods(resParser, lfp);*/
			newbroadcast=calculateCallbackMethods_version2(resParser, lfp);
		}
		System.out.println("Entry point calculation done.");

		// Clean up everything we no longer need
		soot.G.reset();
		return newbroadcast;
	}
	
	
	//由calculateEntrypoints调用 ,罗丹添加，用来在justlooking模式下调用，只找回调，并返回新添加的broadcast
	private Set<String>  calculateCallbackMethods_version2(ARSCFileParser resParser, LayoutFileParser lfp) throws IOException 
	{
		
		Set<String> broadcast=new HashSet<String>();
		AbstractCallbackAnalyzer jimpleClass = null;

		boolean hasChanged = true;
		while (hasChanged) {
			hasChanged = false;

			// Create the new iteration of the main method
			soot.G.reset();
			initializeSoot(true);
			createMainMethod();

			if (jimpleClass == null) {
				// Collect the callback interfaces implemented in the app's
				// source code
				jimpleClass = callbackClasses == null
						? new DefaultCallbackAnalyzer(config, entrypoints, callbackFile)
						: new DefaultCallbackAnalyzer(config, entrypoints, callbackClasses);
				jimpleClass.collectCallbackMethods();

				// Find the user-defined sources in the layout XML files. This
				// only needs to be done once, but is a Soot phase.
				lfp.parseLayoutFile(apkFileLocation);
			} else
				jimpleClass.collectCallbackMethodsIncremental();

			// Run the soot-based operations
			PackManager.v().getPack("wjpp").apply();
			PackManager.v().getPack("cg").apply();
			PackManager.v().getPack("wjtp").apply();

			// Collect the results of the soot-based phases
			for (Entry<String, Set<SootMethodAndClass>> entry : jimpleClass.getCallbackMethods().entrySet()) {
				Set<SootMethodAndClass> curCallbacks = this.callbackMethods.get(entry.getKey());
				if (curCallbacks != null) {
					if (curCallbacks.addAll(entry.getValue()))
						hasChanged = true;
				} else {
					this.callbackMethods.put(entry.getKey(), new HashSet<>(entry.getValue()));
					hasChanged = true;
				}
			}
			
			if (entrypoints.addAll(jimpleClass.getDynamicManifestComponents()))
				hasChanged = true;
				
			        //罗丹修改开始
					//analyzeMethodForDynamicBroadcastReceiver(method);
					if(this.config.getAndroidconfig().getUseEntrypointskind().indexOf("B")>-1)
					{
					   broadcast.addAll(jimpleClass.getDynamicManifestComponents());
					   if (entrypoints.addAll(jimpleClass.getDynamicManifestComponents()))
						     hasChanged = true;
					}
			//罗丹修改结束
		}

		// Collect the XML-based callback methods
		collectXmlBasedCallbackMethods(resParser, lfp, jimpleClass);
				 
				 
		
				
		return broadcast;
	}
	
	
//罗丹添加结束
	//fly
	public Map<String,Set<String>> runInfoflowScan() {
		if (this.sourceSinkProvider == null)
			throw new RuntimeException("Sources and/or sinks not calculated yet");
		InfoflowforScan info;
		if (cfgFactory == null)
			info = new InfoflowforScan(androidJar, forceAndroidJar, null,
					new DefaultPathBuilderFactory(config.getPathBuilder(),
							config.getComputeResultPaths()));
		else
			info = new InfoflowforScan(androidJar, forceAndroidJar, cfgFactory,
					new DefaultPathBuilderFactory(config.getPathBuilder(),
							config.getComputeResultPaths()));
		
		final String path;
		if (forceAndroidJar)
			path = androidJar;
		else
			path = Scene.v().getAndroidJarPath(androidJar, apkFileLocation);

		info.setTaintWrapper(taintWrapper);
		
		info.setConfig(config);
		info.setSootConfig(sootConfig);
		
		if (null != ipcManager) {
			info.setIPCManager(ipcManager);
		}

		return info.computeInfoflow(apkFileLocation, path, entryPointCreator, sourceSinkManager);

	}
	//fly
	
	//罗丹添加,getter,setter方法
	
	public void setCallbackMethods(
			Map<String, Set<SootMethodAndClass>> callbackMethods) {
		this.callbackMethods = callbackMethods;
	}
	public Map<String, Set<SootMethodAndClass>> getCallbackMethods() {
		return callbackMethods;
	}
	
	
   public Set<String> getEntrypoints() {
		return entrypoints;
	}
	public void setEntrypoints(Set<String> entrypoints) {
		this.entrypoints = entrypoints;
	}
 public String getCurrententrypoints() {
		return currententrypoints;
	}
	public void setCurrententrypoints(String currententrypoints) {
		this.currententrypoints = currententrypoints;
	}
   public String getAppPackageName() {
		return appPackageName;
	}
   
   
public void setAppPackageName(String appPackageName) {
	this.appPackageName = appPackageName;
}


//罗丹添加结束

	
}
