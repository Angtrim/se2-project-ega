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

abstract sig TaxiStatus {}

one sig TaxiBusy extends TaxiStatus {}
one sig TaxiAvailable extends TaxiStatus {}

/*************** Facts ***************/

fact allPassengersFit {
	no r: SingleRide | #r.passenger > r.driver.car.seats
	no r: SharedRide | #r.passenger > r.driver.car.seats
}

//each taxi has a maximum number of seats
fact maxTaxiSeats {
	no t: Taxi | t.seats < 1
	no t: Taxi | t.seats > 6
}

//there exists at least one passenger per ride
fact rideHasReasonToExist {
	no r: SingleRide | #r.passenger < 1
	no r: SharedRide | #r.passenger < 1
}

//there exists at least one driver per taxi 
fact taxiCarHasReasonToExist {
	all t: Taxi | one d: TaxiDriver | t in d.car
}

//two different rides can't have the same user

fact userHasOneRide {
	all u: User | lone r: SingleRide | u in r.passenger
	all u: User | lone r: SharedRide | u in r.passenger
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

//if the driver is not in a ride then the taxi associated to that driver is available
fact availability {
	one s: TaxiAvailable | no d: TaxiDriver | some r:Ride | d in r.driver && s in d.status 
}

//if the driver is in a ride then the taxi associated to that driver is TaxiBusy
fact unavailability {
	one s: TaxiBusy | no d: TaxiDriver | some r:Ride | !(d in r.driver) && s in d.status 
}

//it cannot exist a queue not associated with a taxi TaxiZone
//fact eachQueueHasZone {
//	all z: TaxiZone | no q: Queue | !(q in z.queue)
//}

//all queues belong to one queue QueueManager
fact allQueuesBelongToQueueManager {
	all q: Queue | one qm: QueueManager | q in qm.queues
}

//two zones cannot have the same queue 
fact oneZoneOneQueue {
	all q: Queue | one z: TaxiZone | q in z.*queue
}

/*************** Predicates ***************/
pred show {
	#User > 5
	#TaxiDriver > #User
	#Ride < #User
	#SingleRide = 2
	#SharedRide = 2
}

run show for 10