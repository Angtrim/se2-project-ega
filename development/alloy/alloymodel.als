module myTaxiService

/*************** Classes ***************/
abstract sig User {
    status: one UserStatus
}

abstract sig UserStatus {}

lone sig ActiveUserStatus extends UserStatus {}
lone sig InactiveUserStatus extends UserStatus {}

abstract sig Ride {
    driver: one TaxiDriver,
    passenger: some User
}

sig SingleRide extends Ride {} {#passenger = 1}
sig SharedRide extends Ride {} {#passenger > 1}

sig TaxiDriver {
    car: one Taxi,
    status: one TaxiStatus
}


sig TaxiZone {
    queue: one Queue
}

sig Taxi {
    seats: one Int
}

sig Queue {
    driver: some TaxiDriver
}

one sig QueueManager {
    queues: some Queue
}


one sig RidesManager {
    rides: some Ride,
    qm: one QueueManager
}

abstract sig TaxiStatus {}

lone sig TaxiBusy extends TaxiStatus {}
lone sig TaxiAvailable extends TaxiStatus {}

/*************** Facts ***************/

//there are enough seats to accommodate all the passengers 
fact allPassengersFit {
    all r: Ride | #r.passenger =< r.driver.car.seats
}

//each taxi has a maximum number of seats
fact maxTaxiSeats {
    all t: Taxi | quantityIsInBounds[t.seats]
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
    all d: TaxiDriver | isAvailable[d]  implies !( isInRide[d] )  
}

//if the user is active he is in a ride
fact activity {
    all u: User | isActive[u]  iff ( isUserInRide[u] )  
}

//if the driver is available he is in a queue
fact availabilityInQueue {
    all d: TaxiDriver | isAvailable[d] implies !( isNotInQueue[d] )  
}

//if the driver is in a ride then the status is busy 
fact unavailability {
    all d: TaxiDriver | isInRide[d] implies isBusy[d]
}

//if the driver is busy, he is not in a queue
fact noBusyDriverBelongsToQueue {
    all d: TaxiDriver | isBusy[d]  implies isNotInQueue[d]
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
    all r: Ride | one rm: RidesManager | r in rm.rides
}

/*************** Functions ***************/

fun numberOfSeats [r: Ride]: Int {
    r.driver.car.seats
}

/*************** Assertions ***************/

/*************** Predicates ***************/

pred isAvailable [ d: TaxiDriver ] {
    some s: TaxiAvailable | d.status in s
}

pred isActive [ u: User ] {
    some s: ActiveUserStatus | u.status in s
}

pred isBusy [ d: TaxiDriver ] {
    some s: TaxiBusy | d.status in s
}

pred isInactive [ u: User ] {
    some s: InactiveUserStatus | u.status in s
}

pred isInRide [ d: TaxiDriver ] {
    some r:Ride | d in r.driver
}

pred isUserInRide [ u: User ] {
    some r:Ride | u in r.passenger
}

pred isNotInQueue[ d: TaxiDriver]{
    no q:Queue | d in q.driver
}

pred quantityIsInBounds [n: Int] {
    n > 1 && n < 6
}

pred show {
    #SingleRide = 1
    #Ride = 1 
    #TaxiDriver = 3
    #User = 5
}

run show for 10
