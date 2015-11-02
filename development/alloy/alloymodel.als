module myTaxiService

/* class declaration */

sig GenericText {}

sig User {
	ID: one GenericText,
}

sig Ride {
	passenger: some User,
	driver: one TaxiDriver
}

sig TaxiDriver {
	ID: one GenericText,
	license: one GenericText,
	car: one Taxi
}

sig Taxi {
	seats: one Int,
	plate: one GenericText
} {#seats >= 1 && #seats <= 6} 

sig TaxiStatus {
	driver: one TaxiDriver
}

sig Queue {
	driver: some TaxiDriver,
}

sig QueueManager {
	queues: some Queue
}

//facts

fact allPassengersFit {
	no r: Ride | r.passenger > r.driver.car.seats
}

//there exists at least one passenger per ride
fact rideHasReasonToExist {
	no r: Ride | #r.passenger < 1
}

//a user must belong to at most one active ride
fact oneUserOneRide {
	no 
}


//run
pred show {}

run show for 3 but 1 QueueManager