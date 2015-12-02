
#this algorithm is created to manage the queue of taxi driver with clear and right rules.

from math import *

#the driver class that hold all the data and a precendence factor that will be update during the algorithm
class TaxiDriver:
	precedenceFactor = 0
	def __init__(self, ID, (x,y), inactiveTime):
		self.ID = ID
		self.coordinates = (x,y)
		self.inactiveTime = inactiveTime
	
#calculate the euclidean distance, obviously it will be replaced by the google maps api to calculate the distance
def calculateDistance((x1,y1), (x2, y2)):
	return sqrt(pow(x2-x1,2)+pow(y2-y1,2))

#sample data
taxiDriver = [TaxiDriver("DSIOA", (50,45), 59), TaxiDriver("GIAOND", (60,12), 45), TaxiDriver("PINGU", (90,34), 80)]
requestPosition = (89, 67)
cellDiagonal = 100

bestPrecendenceFactor = 0
selectedDriver = 0

#for every taxi driver in the list it checks which one has the best precedence factor that is create composing the 
#inactive time and the distance from the user with a configurable weight (in the sample is 0.2 and 0.8)
for i in taxiDriver: 
	i.precedenceFactor = ((cellDiagonal - calculateDistance(i.coordinates, requestPosition))*20 + i.inactiveTime*80)/100

	if bestPrecendenceFactor > i.precedenceFactor or bestPrecendenceFactor == 0:
		bestPrecendenceFactor = i.precedenceFactor
		selectedDriver = i

print(i.ID)




