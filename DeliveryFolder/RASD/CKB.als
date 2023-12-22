-- Enumerations 

enum TournamentLifeCycle { 
	tCreated, 
	tOpened, 
	tClosed 
}

enum BattleLifeCycle { 
	bCreated, 
	bOpened, 
	bEvaluation, 
	bClosed 
}

enum QualityAspect { 
	reliability, 
	maintanability, 
	security 
}

enum RequestStatus {
	pending,
	accepted,
	rejected	
}

enum BattleRequestStatus {
	brPending,
	brAccepted,
	brRejected
}

-- Signatures

sig Str, Timestamp, FileCollection {}

abstract sig Guest {}

abstract sig Participant extends Guest {
	firstName: one Str,
	lastName: one Str, 
	email: disj one Str, 
	password: one Str
}

sig ProgrammingLanguage {
	name: disj one Str
}

sig Student extends Participant {
	username: disj one Str,
	learns: some ProgrammingLanguage
}

sig Educator extends Participant {
	affiliate: some Institution,
	institutionalBackground: one Str,
	institutionalBackgroundFiles: disj one FileCollection,
	createsT: set Tournament
}

sig Institution {
	name: disj one Str
}

sig Tournament {
	creator: one Educator,
	helpers: set Educator, -- ciao
	name: disj one Str, 
	basedOn: one ProgrammingLanguage,
	creationTime: one Timestamp, 
	regDeadline: one Timestamp,  
	status: one TournamentLifeCycle,
	contains: disj some Battle
} {
	creationTime != regDeadline 
	creator not in helpers --
}

sig Battle {
	createdIn: one Tournament,
	creator: one Educator,
	name: disj one Str,
	creationTime: one Timestamp, 
	regDeadline: one Timestamp, 
	finalSubDeadline: one Timestamp,
	minTeamSize: one Int, 
	maxTeamSize: one Int, 
	additionalScoringConfigs: one Str, 
	evaluatedOn: set QualityAspect, 
	has: disj one CodeKata,
	status: BattleLifeCycle,
	exploits: set StaticSystemTool
} {
	minTeamSize > 0 
	maxTeamSize > 0 
	minTeamSize < maxTeamSize
	#evaluatedOn > 0 implies #exploits > 0
	#evaluatedOn >= #exploits
}

sig CodeKata {
	description: disj one Str,
	testCases: disj one FileCollection, 
	automationScripts: disj one FileCollection
} {
	testCases != automationScripts
}

sig StaticSystemTool {
	evaluates: some QualityAspect,
	accepts: some ProgrammingLanguage,
	monitors: set Battle
}

sig Team {
	id: disj one Str, 
	participates: one Battle,
	creationTime: one Timestamp, 
	isComposedBy: disj some BattleEnrollment,
	has: disj one GitHubRepository,
	battleScore: one Int
} {
	participates.minTeamSize <= #isComposedBy
	participates.maxTeamSize >= #isComposedBy
	battleScore > 0 
}

sig GitHubRepository {
	url: disj one Str, 
	sources: disj one FileCollection
}

sig EnrolledStudent {
	student: one Student, 
	tournament: one Tournament,
	creationTime: one Timestamp,
	tournamentScore: one Int
} {
	tournamentScore >= 0
	creationTime = tournament.regDeadline
}

sig BattleEnrollment {
	enrolledStudent: one EnrolledStudent, 
	battle: one Battle, 
	battleScore: one Int, 
	creationTime: one Timestamp,
	status: one BattleRequestStatus
} {
	battle in enrolledStudent.tournament.contains
}

sig TeamFormationRequest {
	sender: one BattleEnrollment, 
	receiver: one BattleEnrollment, 
	battle: one Battle,
	status: one RequestStatus
} {
	sender != receiver
	sender.battle = receiver.battle
	status = pending and battle.minTeamSize > 1 
		implies sender.status = brPending and
		receiver.status = brPending
	status = rejected and battle.minTeamSize = 1 
		implies sender.status = brAccepted and
		receiver.status = brRejected
	status = rejected and battle.minTeamSize > 1 
		implies sender.status = brRejected and
		receiver.status = brRejected
	status = accepted implies
		sender.status = brAccepted and
		receiver.status = brAccepted
	(status = pending and battle.minTeamSize = 1) 
	implies sender.status = brAccepted and
	receiver.status = brPending
}

sig TournamentHelpRequest {
	sender: one Educator, 
	receiver: one Educator, 
	tournament: one Tournament,
	status: one RequestStatus
} {
	sender != receiver
	sender = tournament.creator
	status = accepted implies
		receiver in tournament.helpers
	status = rejected or status = pending implies
		receiver not in tournament.helpers
}

-- fact 

fact everyProgLangAtLeastOneStudent {
	all p: ProgrammingLanguage | some s: Student | p in s.learns
}

fact everyInstitutionOneEducator {
	all i: Institution | some e: Educator | i in e.affiliate
}

fact everyTournamentOneEducator {
	all t: Tournament | one e: Educator | t in e.createsT and t.creator = e
}

fact everyBattleOneTournament {
	all b: Battle | one t: Tournament | b in t.contains and b.createdIn = t
}

fact everyAspectAtLeastBattle {
	all q: QualityAspect | some b: Battle | q in b.evaluatedOn
}

// There is only one tournament creator
fact {
	no disj e1, e2: Educator | one t: Tournament |
	t in e1.createsT and t in e2.createsT
}

fact coherenceSSTsBattles {
	all sst: StaticSystemTool | all b: Battle | 
	b in sst.monitors implies 
	b.createdIn.basedOn in sst.accepts
}

fact everySSTatLeastOneBattle {
	all sst: StaticSystemTool | one b: Battle |
	b in sst.monitors and sst in b.exploits 
}

fact everyQualityAspectOfABattleIsMonitored {
	all b: Battle, q: QualityAspect |
	q in b.evaluatedOn implies 
	one sst: StaticSystemTool | 
	q in sst.evaluates and 
	b in sst.monitors
}

// If a battle has a certain quality aspect, 
// there is only one security system tool that can analyze it
fact {
	no disj sst1, sst2: StaticSystemTool | all b: Battle |
	b.evaluatedOn in sst1.evaluates and 
	b.evaluatedOn in sst2.evaluates 	
}

fact SSTcoeherentWithTournamentProgLang {
	all sst: StaticSystemTool | one b: Battle |
	b.createdIn.basedOn in sst.accepts
}

fact {
	all t: Team, be: BattleEnrollment |
	be in t.isComposedBy implies be.status = brAccepted
}

fact {
	all tfr: TournamentHelpRequest |
	tfr.status = accepted implies tfr.receiver in tfr.tournament.helpers 
}

fact {
	all tfr: TournamentHelpRequest |
	(tfr.status = rejected or tfr.status = pending) 
	implies tfr.receiver not in tfr.tournament.helpers 
}

fact {
	all e: Educator, t: Tournament | 
	e in t.helpers implies 
	(one thr: TournamentHelpRequest |
	thr.receiver = e and 
	thr.status = accepted and
	thr.sender = t.creator)
}

fact disjointEnrolledStudents {
	no disj t1, t2: EnrolledStudent |
	t1.student = t2.student and
	t1.tournament = t2.tournament
}

fact disjointBattleEnrollments {
	no disj be1, be2: BattleEnrollment |
	be1.enrolledStudent = be2.enrolledStudent and 
	be1.battle = be2.battle 
}

fact disjointTournamentHelpRequests {
	no disj t1, t2: TournamentHelpRequest |
	t1.sender = t2.sender and
	t1.receiver = t2.receiver 
}

fact onlyAcceptedOne {
	all t: Team, be: BattleEnrollment |
	be in t.isComposedBy implies be.status = brAccepted
}
-- Assertions 



-- Worlds 

pred w1 {
	#EnrolledStudent = 4
	#Educator = 1
	#Tournament = 1
	#Team = 2
	#Battle = 1
}

pred w2 {
	#Educator = 3
	#Tournament = 2
	#Battle = 5
	#Team = 4
	one t: TournamentHelpRequest | t.status = accepted
	one t: TeamFormationRequest | t.status = accepted
	one be: BattleEnrollment | be.status = brRejected
	one be: BattleEnrollment | be.status = brPending
}

pred w3 {
	#Educator = 3
	#Tournament = 4
	#Battle = 5
	#Team = 6
	one t: TournamentHelpRequest | t.status = accepted
	one t: TournamentHelpRequest | t.status = rejected
	one t: TeamFormationRequest | t.status = accepted
	one be: BattleEnrollment | be.status = brRejected
	one t: TeamFormationRequest | t.status = pending
}

run w2 for 15
