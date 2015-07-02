import subprocess
from os import walk
import sys
from datetime import datetime
	
# global settings
libPath = "../Prelude/"				# imported library path
FUTPath1 = "../ATL_Rule_Encoding/"	# test task 1

tasks = [FUTPath1]

def loadDataSet(path):
	f = []
	for (dirpath, dirnames, filenames) in walk(path):
		f.extend(filenames)
		break
	return f
	
def processFile(f):
	specLoC = 0
	specEnd = False
	implLoC = 0
	implStart = False
	for line in f:
		if line.startswith("procedure") and not specEnd:
			specLoC = specLoC+1
		if not specEnd:
			specLoC = specLoC+1	
		if line.startswith("implementation"):
			specEnd = True
			implStart = True
			implLoC = implLoC+1
		if implStart:
			implLoC = implLoC+1
	print "%s | %s | %s" % (f.name, specLoC-2, implLoC)
	
def BatchLineCounter():
	for task in tasks:
		print "Folder: "+task
		fileNames = loadDataSet(task)
		for file in fileNames:
			filepath = task+file
			with open(filepath) as f:
				processFile(f)



def main():
	i = datetime.now()
	print "Regression Tests start at: "+i.strftime('%Y/%m/%d %H:%M:%S')
	print " ========================================================================= "
	BatchLineCounter()
	
if __name__ == "__main__":
    main()