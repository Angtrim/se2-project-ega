
#queue algorithm 
from math import *

class TaxiDriver:
	precedenceFactor = 0
	def __init__(self, ID, (x,y), inactiveTime):
		self.ID = ID
		self.coordinates = (x,y)
		self.inactiveTime = inactiveTime
	

def calculateDistance((x1,y1), (x2, y2)):
	return sqrt(pow(x2-x1,2)+pow(y2-y1,2))


taxiDriver = [TaxiDriver("DSIOA", (50,45), 59), TaxiDriver("GIAOND", (60,12), 45), TaxiDriver("PINGU", (90,34), 80)]
requestPosition = (89, 67)
cellDiagonal = 100

bestPrecendenceFactor = 0
selectedDriver = 0

for i in taxiDriver: 
	i.precedenceFactor = ((cellDiagonal - calculateDistance(i.coordinates, requestPosition))*20 + i.inactiveTime*80)/100

	if bestPrecendenceFactor > i.precedenceFactor or bestPrecendenceFactor == 0:
		bestPrecendenceFactor = i.precedenceFactor
		selectedDriver = i

print(i.ID)




