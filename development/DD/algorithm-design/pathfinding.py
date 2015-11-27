
class User:
	ID = "UserID"
	path = [(0,192), (34,90)]
	hasSharingRideEnable = True
	compatibleUserList = [User, User, ...]

usersWithAPendingSharingRequestList = [user1, user2, user3]

def calculateEstimatedPrice(path):
	#google gives this kind of API https://developers.google.com/maps/documentation/directions/intro#traffic-model
	travelTime = GoogleMapsAPI.travelTime(path)
	price = travelTime*costPerMinute
	return price

def pathAreCompatible(path1, path2):
	return getZone(path1[0]) == getZone(path2[0]) and
	 (getZone(path1[0]) in getZoneList(path2) or 
	 	getZone(path2[0]) in getZoneList(path1)) 

def matchUser(users):
	users[0].compatibleUserList.append(users[1])
	users[1].compatibleUserList.append(users[0])
	sendNotificationOnCompatibilityFound(users)

#supposing that till now no matches has been found for the current waiting list
requestingUser = User
requestingUserPrice = calculateEstimatedPrice()

for waitingUser in usersWithAPendingSharingRequestList:
	tempCompositePath = requestingUser.path.append(waitingUser.path)
	#starting from the same zone and the end of one of them is in the path of the other
	if(pathAreCompatible(requestingUser.path, waitingUser.path))
		matchUsers([requestingUser, waitingUser])



