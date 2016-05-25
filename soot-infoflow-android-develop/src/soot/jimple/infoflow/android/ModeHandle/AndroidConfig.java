package soot.jimple.infoflow.android.ModeHandle;

public class AndroidConfig {
	
	//fly 修改
	private boolean selectSource=false;
	public boolean getSelectSource(){
		return selectSource;
	}
	public void setSelectSource(boolean selectSource){
		this.selectSource=selectSource;
	}
	
	private boolean saveSource = false;
	public boolean getSaveSource(){
		return saveSource;
	}
	public void setSaveSource(boolean saveSource){
		this.saveSource=saveSource;
	}
		
	//fly 
    
	    //罗丹添加，添加5参数
		private boolean  useCallbacksconfig= false;
		private boolean  useEntrypointsconfig= false;
		private String  useEntrypointskind= "ABCSP";
		private String testOnebyoneentrypoints="";
		private boolean  printDummymain= false;
		private boolean  printEntryAndCallbacksConfig= false;
		
		
		//罗丹添加测试参数，添加5参数
		private boolean justLookingXmlEntrypoints=false;
		private boolean justLookingEntrypointsAndCallbackOnebyone=false;
		private boolean printTestConfig=false;
		private int  callbackstep;
		
		
		public boolean isPrintEntryAndCallbacksConfig() {
			return printEntryAndCallbacksConfig;
		}
		public void setPrintEntryAndCallbacksConfig(boolean printEntryAndCallbacksConfig) {
			this.printEntryAndCallbacksConfig = printEntryAndCallbacksConfig;
		}
		public boolean isUseCallbacksconfig() {
			return useCallbacksconfig;
		}
		public void setUseCallbacksconfig(boolean useCallbacksconfig) {
			this.useCallbacksconfig = useCallbacksconfig;
		}
		public boolean isUseEntrypointsconfig() {
			return useEntrypointsconfig;
		}
		public void setUseEntrypointsconfig(boolean useEntrypointsconfig) {
			this.useEntrypointsconfig = useEntrypointsconfig;
		}
		public String getUseEntrypointskind() {
			return useEntrypointskind;
		}
		public void setUseEntrypointskind(String useEntrypointskind) {
			this.useEntrypointskind = useEntrypointskind;
		}
		public String getTestOnebyoneentrypoints() {
			return testOnebyoneentrypoints;
		}
		public void setTestOnebyoneentrypoints(String testOnebyoneentrypoints) {
			this.testOnebyoneentrypoints = testOnebyoneentrypoints;
		}
		public boolean isPrintDummymain() {
			return printDummymain;
		}
		public void setPrintDummymain(boolean printDummymain) {
			this.printDummymain = printDummymain;
		}
		public boolean isJustLookingXmlEntrypoints() {
			return justLookingXmlEntrypoints;
		}
		public void setJustLookingXmlEntrypoints(boolean justLookingXmlEntrypoints) {
			this.justLookingXmlEntrypoints = justLookingXmlEntrypoints;
		}
		public boolean isJustLookingEntrypointsAndCallbackOnebyone() {
			return justLookingEntrypointsAndCallbackOnebyone;
		}
		public void setJustLookingEntrypointsAndCallbackOnebyone(
				boolean justLookingEntrypointsAndCallbackOnebyone) {
			this.justLookingEntrypointsAndCallbackOnebyone = justLookingEntrypointsAndCallbackOnebyone;
		}
		public boolean isPrintTestConfig() {
			return printTestConfig;
		}
		public void setPrintTestConfig(boolean printTestConfig) {
			this.printTestConfig = printTestConfig;
		}
		public int getCallbackstep() {
			return callbackstep;
		}
		public void setCallbackstep(int callbackstep) {
			this.callbackstep = callbackstep;
		}
		
		
		
}
