module myTaxiService

/*************** Classes ***************/

/*This is a class that stands for all the alphanumeric codes*/
one sig GenericString {}

sig User {
	ID: one GenericString
}

abstract sig Ride {
	driver: one TaxiDriver
}

sig SingleRide extends Ride {
	passenger: one User
}

sig SharedRide extends Ride {
	passenger: some User
} {#passenger > 1}

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

fact allPassengersFit {
	no r1: SingleRide | #r1.passenger > r1.driver.car.seats
	no r2: SharedRide | #r2.passenger > r2.driver.car.seats
}

//each taxi has a maximum number of seats
fact maxTaxiSeats {
	no t1: Taxi | t1.seats < 1
	no t2: Taxi | t2.seats > 6
}

//there exists at least one passenger per ride
fact rideHasReasonToExist {
	no r1: SingleRide | #r1.passenger < 1
	no r2: SharedRide | #r2.passenger < 2
}

//there exists at least one driver per taxi 
fact taxiCarHasReasonToExist {
	all t: Taxi | one d: TaxiDriver | t in d.car
}

//two different rides can't have the same user

fact userHasOneRide {
	all u: User | lone r: SingleRide | lone sr: SharedRide | u in r.passenger+sr.passenger
}

//two different queues can't have the same taxi driver
fact uniqueQueue {
	all t: TaxiDriver | lone q: Queue | t in q.driver
}

//two different taxi drivers can't have the same car
fact uniqueQueue {
	all t: Taxi | lone d: TaxiDriver | t in d.car
}

//two rides can't have the same driver
fact uniqueDrive {
	all d: TaxiDriver | lone r: Ride | d in r.driver
}

//if the driver is not in a ride then the status is available
fact availability {
	one s: TaxiAvailable | no d: TaxiDriver | some r:Ride | d in r.driver && s in d.status 
}

/*
//if the driver is in a ride then the taxi associated to that driver is busy
fact unavailability {
	one s: TaxiBusy | no d: TaxiDriver | some r:Ride | !(d in r.driver) && s in d.status 
}
*/

//no busy driver can ever belong to a queue
fact noBusyDriverBelongsToQueue {
	one s: TaxiBusy | all q: Queue | no t: TaxiDriver | t.status = s && t in q.driver
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
fact allRidesBelongToQueueManager {
	all r: Ride | one rm: RideManager | r in rm.rides
}

/*************** Predicates ***************/
pred show {
	#Ride > 1
}

run show for 10