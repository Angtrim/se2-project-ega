module myTaxiService

/*************** Classes ***************/

/*This is a class that stands for all the alphanumeric codes*/
one sig GenericString {}

sig User {
	ID: one GenericString
}

abstract sig Ride {
	driver: one TaxiDriver,
	passenger: some User
}

sig SingleRide extends Ride {

}

sig SharedRide extends Ride {

} 

sig TaxiDriver {
	ID: one GenericString,
	license: one GenericString,
	car: one Taxi,
	status: one TaxiStatus
}


sig TaxiZone {
	ID: one GenericString,
	queue: one Queue
}

sig Taxi {
	seats: one Int,
	plate: one GenericString
}

sig Queue {
	driver: some TaxiDriver,
}

one sig QueueManager {
	queues: some Queue
}


one sig RideManager {
	rides: some Ride
}

abstract sig TaxiStatus {}

one sig TaxiBusy extends TaxiStatus {}
one sig TaxiAvailable extends TaxiStatus {}

/*************** Facts ***************/

// Single Ride has exactly one user
fact singleRideHasOneUser{
	no r : SingleRide | #r.passenger != 1
}

fact sharedRideHasMoreThanOneUser {
	no r : SharedRide | #r.passenger = 1
}

fact allPassengersFit {
	no r: Ride | #r.passenger > r.driver.car.seats
}

//each taxi has a maximum number of seats
fact maxTaxiSeats {
	no t1: Taxi | t1.seats < 1
	no t2: Taxi | t2.seats > 6
}

//there exists at least one passenger per ride
fact rideHasReasonToExist {
	no r: SingleRide | #r.passenger < 1
}

//there exists at least one driver per taxi 
fact taxiCarHasReasonToExist {
	all t: Taxi | one d: TaxiDriver | t in d.car
}

//two different rides can't have the same user
fact userHasOneRide {
	all u: User | lone r: Ride | u in r.passenger
}

//two different queues can't have the same taxi driver
fact uniqueQueueForDriver {
	all d: TaxiDriver | lone q: Queue | d in q.driver
}

//two different taxi drivers can't have the same car
fact uniqueTaxi{
	all t: Taxi | lone d: TaxiDriver | t in d.car
}

//two rides can't have the same driver
fact uniqueDrive {
	all d: TaxiDriver | lone r: Ride | d in r.driver
}

//if the driver is available he is not in a ride
fact availability {
    all d: TaxiDriver | isAvailable[d] => !( isInRide[d] )  
}

//if the driver is available he is in a queue
fact availability {
    all d: TaxiDriver | isAvailable[d] => !( isNotInQueue[d] )  
}

//if the driver is in a ride then the status is busy 
fact unavailability {
	 all d: TaxiDriver | isInRide[d] => isBusy[d]
}

//if the driver is busy, he is not in a queue
fact noBusyDriverBelongsToQueue {
	all d: TaxiDriver | isBusy[d] => isNotInQueue[d]
} 

//all queues belong to the QueueManager
fact allQueuesBelongToQueueManager {
	all q: Queue | one qm: QueueManager | q in qm.queues
}

//two zones cannot have the same queue 
fact oneZoneOneQueue {
	all q: Queue | one z: TaxiZone | q in z.*queue
}


//all rides belong to the RideManager
fact allRidesBelongToRideManager {
	all r: Ride | one rm: RideManager | r in rm.rides
}

/*************** Assertions ***************/
/*
assert availableDriver {
	some d: TaxiDriver | one s: TaxiBusy | some q: Queue | d.status = s && d in q.driver
}

check availableDriver for 10
*/
/*************** Predicates ***************/

pred isAvailable [ d: TaxiDriver ] {
	some s: TaxiAvailable | d.status in s
}

pred isBusy [ d: TaxiDriver ] {
	some s: TaxiBusy | d.status in s
}

pred isInRide [ d: TaxiDriver ] {
	some r:Ride | d in r.driver
}

pred isNotInQueue[ d: TaxiDriver]{
	no q:Queue | d in q.driver
}




pred show {
 
}



run show for 10
