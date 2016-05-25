package soot.jimple.infoflow;

public class InfoflowConfig_self {

	//罗丹添加，添加4参数
  
	
	private  boolean usingChange=false;  //罗丹备注：输出改变，不使用icfg
	private boolean justPrintresultnum=false;
	
	

	

	public boolean isUsingChange() {
		return usingChange;
	}

	public void setUsingChange(boolean usingChange) {
		this.usingChange = usingChange;
	}

	public boolean isJustPrintresultnum() {
		return justPrintresultnum;
	}

	public void setJustPrintresultnum(boolean justPrintresultnum) {
		this.justPrintresultnum = justPrintresultnum;
	}
	
	
	
}
