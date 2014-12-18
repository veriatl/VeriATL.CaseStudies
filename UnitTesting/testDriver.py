import subprocess
from os import walk
import sys
from datetime import datetime
	
# global settings
libPath = "../Prelude/"				# imported library path
FUTPath1 = "../ATL_Rule_Encoding/"	# test task 1
FUTPath2 = "../ATL_Correctness/"	# test task 2

tasks = [FUTPath1, FUTPath2]		# test tasks to run

def forgeRunningCommand(fName):
	command = []

	command.append("Boogie")					# command
	command.append("/nologo")					# option

	command.append(libPath+"Instr.bpl")			# importing library
	command.append(libPath+"LibOCL.bpl")
	command.append(libPath+"Metamodels.bpl")
	command.append(libPath+"NativeLib.bpl")

	command.append(fName)	# input
	
	return command

def loadDataSet(path):
	f = []
	for (dirpath, dirnames, filenames) in walk(path):
		f.extend(filenames)
		break
	return f

def loadOracle(fn):
	f = open(fn+".expect")
	lines = f.readline()
	f.close()

	return lines

def BatchTest(isDetailed):
	failedTasks = []
	
	for task in tasks:
			print "Folder: "+task
			filesNames = loadDataSet(task)
			
			for fn in filesNames:
				# get output by execute boogie against input
				myCmd = forgeRunningCommand(task+fn)
				p = subprocess.Popen(myCmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE) 
				out, err = p.communicate()

				lastLine = out.strip().split('\n')[-1]
				
				# get oracle
				expect = loadOracle(fn)
				
				sys.stdout.write("\tchecking "+fn)
				sys.stdout.flush()
				# compare
				if lastLine == expect:
					print " [pass]"
				else:
					print " [failed]"
					failedTasks.append([task,fn])
			
	
	if (isDetailed) :
		for failedTask in failedTasks:
			t = failedTask[0]
			f = failedTask[1]
			executeSingle(t,f)
	

def executeSingle(task,fn):
	print 
	print 
	print 
	print "FAILED TASK: "+ task + fn
	myCmd = forgeRunningCommand(task+fn)
	p = subprocess.Popen(myCmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE) 
	out, err = p.communicate()

	
	lastLine = out.strip().split('\n')[-1]
	

	# get oracle
	expect = loadOracle(fn)
	
	
	print " ========================================================================= "
	print " * Real:" + lastLine
	print " * Expected: "+ expect	
	print " ========================================================================= "
	

def main():
	i = datetime.now()
	print "Regression Tests start at: "+i.strftime('%Y/%m/%d %H:%M:%S')
	print " ========================================================================= "
	BatchTest(True)
	

if __name__ == "__main__":
    main()
	
	
