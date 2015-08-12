import subprocess
from os import walk
import sys
from datetime import datetime
	
# global settings start
# VERIFICATION OPTION ON PROJECTS
_OPT_VERIFICATION = 1		# CORRECTNESS VERIFICATION
_OPT_VALIDATION = 2			# TRANSLATION VALIDITON


LibsPath = "../Prelude/"		# imported library path


# PROJ PATH
Proj1 = "../_HSM2FSM/"			# task 1
Proj2 = "../_ER2REL/"			# task 2
Proj3 = "../_ResolveTemp/"		# task 3

# PROJ TO VERIFY
Projs = [Proj2]	

# WHAT OPTION TO VERIFY EACH PROJ
Projs_option_map = { Proj1: {_OPT_VALIDATION}, 
                     Proj2: {_OPT_VALIDATION,_OPT_VERIFICATION},    
                     Proj3: {_OPT_VERIFICATION}    }

# BOOGIE ARGS
Boogie_cmd = {"/nologo"}

# global settings end

# forge the cmd that executes Boogie, depending on the [option] that pass in, which stores at task_option_map.
def forgeRunningCommand(projPath, taskName, option):
	command = []

	command.append("boogie")					# command
	
	for opt in Boogie_cmd:						# load extra command args of Boogie
		command.append(opt)
	
	for libName in loadFiles(LibsPath):
		command.append(LibsPath+libName)			# importing library

	command.append(projPath+"Metamodel/Metamodels.bpl")
	
	if option ==_OPT_VERIFICATION :
		command.append(projPath+"ExecutionSemantics/ATLRules.whole.bpl")
		command.append(projPath+"ATL_Correctness/"+taskName)
	elif option == _OPT_VALIDATION :
		command.append(projPath+"ATL_Rule_Encoding/"+taskName)	# input

	return command

# Helper to generate Oracle
def genOracle(todo):	
	for proj in todo:
			print "Folder: "+proj

			for opt in Projs_option_map[proj]:
				if opt == _OPT_VERIFICATION:
					tasks = loadFiles(proj+"/ATL_Correctness/")		
				elif opt == _OPT_VALIDATION:
					tasks = loadFiles(proj+"/ATL_Rule_Encoding/")	
				else:
					break;
			
				for task in tasks:
					myCmd = forgeRunningCommand(proj, task, opt)
					p = subprocess.Popen(myCmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE) 
					out, err = p.communicate()

					lastLine = out.strip().split('\n')[-1]
					
					sys.stdout.write("\twriting oracle \n"+task)
					sys.stdout.flush()
					
					file_ = open(proj+"UnitTesting/"+task+".expect", 'w')
					file_.write(lastLine)
					file_.close()

	
def loadFiles(path):
	f = []
	for (dirpath, dirnames, filenames) in walk(path):
		f.extend(filenames)
		break
	return f

def loadOracle(proj,fn):
	f = open(proj+"UnitTesting/"+fn+".expect")
	lines = f.readline()
	f.close()

	return lines

def BatchTest(isDetailed):
	failedTasks = []
	
	for proj in Projs:
			print "Folder: "+proj

			for opt in Projs_option_map[proj]:
				
				if opt == _OPT_VERIFICATION:
					print "  /ATL_Correctness/"
					tasks = loadFiles(proj+"/ATL_Correctness/")		
				elif opt == _OPT_VALIDATION:
					print "  /ATL_Rule_Encoding/"
					tasks = loadFiles(proj+"/ATL_Rule_Encoding/")	
				else:
					break;
			
				for task in tasks:
					myCmd = forgeRunningCommand(proj, task, opt)
			
					
					p = subprocess.Popen(myCmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE) 
					out, err = p.communicate()

					lastLine = out.strip().split('\n')[-1]
					
					# get oracle
					expect = loadOracle(proj, task)
					
					sys.stdout.write("\tchecking "+task)
					sys.stdout.flush()
					# compare
					if lastLine == expect:
						print " [pass]"
					else:
						print " [failed]"
						executeSingle(proj,task,opt)
						#failedTasks.append([proj,task,opt])
			
	
	if (isDetailed) :
		for failedTask in failedTasks:
			failed_proj = failedTask[0]
			failed_task = failedTask[1]
			failed_task_opt = failedTask[2]
			executeSingle(failed_proj,failed_task,failed_task_opt)
	

def executeSingle(proj,task,opt):
	print 
	print 
	print 
	print "FAILED CASE: %s, %s"%(proj,task)
	myCmd = forgeRunningCommand(proj, task, opt)
	p = subprocess.Popen(myCmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE) 
	out, err = p.communicate()

	
	lastLine = out.strip().split('\n')[-1]
	

	# get oracle
	expect = loadOracle(proj, task)
	
	
	print " ========================================================================= "
	print " * Real:" + lastLine
	print " * Expected: "+ expect	
	print " ========================================================================= "
	
# Generate a project skeleton with the given name as Entry.
# def genFolder(name):
	
def main():
	i = datetime.now()
	print "Regression Tests start at: "+i.strftime('%Y/%m/%d %H:%M:%S')
	print " ========================================================================= "
	
	BatchTest(True)
	
	#genOracle([Proj1])
	
	

if __name__ == "__main__":
    main()
	
	
