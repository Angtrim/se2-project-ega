
class Point:
	def __init__(self,x,y):
		self.x = x
		self.y = y

class TaxiZone:
	taxiList = 0
	def __init__(self, ID, vertices):
		self.ID = ID
		self.vertices = vertices

class TaxiDriver:
	precedenceFactor = 0
	def __init__(self, ID, (x,y), inactiveTime):
		self.ID = ID
		self.coordinates = (x,y)
		self.inactiveTime = inactiveTime

taxiZones = a list of all the zone

#this function will be periodically called from QueueManager 
def updateTaxiQueues(listOfAllTheTaxiDrivers):
	for driver in listOfAllTheTaxiDrivers:
		for zone in taxiZones:
			if zone.region.contains(driver.coordinates):
				zone.taxiList.append(driver)
				break

