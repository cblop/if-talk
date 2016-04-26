%
% -------------------------------PART 1-------------------------------
%
%
% Standard prelude for story
%
% suppress clingo warnings in absence of inertials, non-inertials or obligations
ifluent(0,0).
nifluent(0,0).
oblfluent(0,0).
% fluent rules
holdsat(P,In,J):- holdsat(P,In,I),not terminated(P,In,I),
    next(I,J),ifluent(P, In),instant(I),instant(J), inst(In).
holdsat(P,In,J):- initiated(P,In,I),next(I,J),
    ifluent(P, In),instant(I),instant(J), inst(In).
holdsat(P,In,J):- initiated(P,In,I),next(I,J),
    oblfluent(P, In),instant(I),instant(J), inst(In).
% all observed events occur
occurred(E,In,I):- evtype(E,In,ex),observed(E,In,I),instant(I), inst(In).
% produces null for unknown events
occurred(null,In,I) :- not evtype(E,In,ex), observed(E,In,I),
    instant(I), inst(In).
% produces gap warning for unknown events
unknown(E, In, I) :- not evtype(E,In,ex), observed(E,In,I),
    instant(I), inst(In).
warninggap(In, I) :- unknown(E,In,I), inst(In), instant(I).
% a violation occurs for each non-permitted action
occurred(viol(E),In,I):-
    occurred(E,In,I),
    evtype(E,In,ex),
    not holdsat(perm(E),In,I),
    holdsat(live(In),In,I),evinst(E,In),
    event(E),instant(I),event(viol(E)),inst(In).
occurred(viol(E),In,I):-
    occurred(E,In,I),
    evtype(E,In,inst),
    not holdsat(perm(E),In,I),
    event(E),instant(I),event(viol(E)), inst(In).
% needed until I tidy up some of the constraint generation
% true.
start(0).
instant(0..T) :- final(T).
next(T,T+1) :- instant(T).
final(horizon).
% externals for individual institutions
% #external observed(E,I) : event(E), inst(I). removed 20160415 JAP
% observed(E,I,J) :- observed(E,I), start(J). removed 20160415 JAP
#external holdsat(F,I) : fluent(F,I), inst(I).
holdsat(F,I,J) :- holdsat(F,I), start(J).
#external holdsat(perm(E),I) : event(E), inst(I).
holdsat(perm(E),I,J) :- holdsat(perm(E),I), start(J).
#external holdsat(pow(E),I) : event(E), inst(I).
holdsat(pow(I,E),I,J) :- holdsat(pow(E),I), start(J).
% and for coordinated institutions
#external observed(E) : event(E).
compObserved(E,J) :- observed(E), start(J).

%
% Rules for Institution story
%
  ifluent(live(story), story).
  fluent(live(story), story).
  inst(story).
%
% Constraints for observable events
%
%%  mode COMPOSITE is chosen:
{compObserved(E, J)}:- evtype(E,In,ex),instant(J), not final(J), inst(In).
:- compObserved(E,J),compObserved(F,J),instant(J),evtype(E,InX,ex),
   evtype(F,InY,ex), E!=F,inst(InX;InY). 
obs(I):- compObserved(E,I),evtype(E,In,ex),instant(I),inst(In).
      :- not obs(I), not final(I), instant(I), inst(In).
observed(E,In,I) :- compObserved(E,I), inst(In), instant(I).
%
% Exogenous events
% Event: go (type: ex)
  event(go(Agent0,PlaceName1)) :- agent(Agent0),placename(PlaceName1).
  evtype(go(Agent0,PlaceName1),story,ex) :- agent(Agent0),placename(PlaceName1).
  evinst(go(Agent0,PlaceName1),story) :- agent(Agent0),placename(PlaceName1).
  ifluent(perm(go(Agent0,PlaceName1)), story) :- agent(Agent0),placename(PlaceName1).
  fluent(perm(go(Agent0,PlaceName1)), story) :- agent(Agent0),placename(PlaceName1).
  event(viol(go(Agent0,PlaceName1))) :- agent(Agent0),placename(PlaceName1).
  evtype(viol(go(Agent0,PlaceName1)), story, viol) :- agent(Agent0),placename(PlaceName1).
  evinst(viol(go(Agent0,PlaceName1)),story) :- agent(Agent0),placename(PlaceName1).
% Event: meet (type: ex)
  event(meet(Agent0,Agent1)) :- agent(Agent0),agent(Agent1).
  evtype(meet(Agent0,Agent1),story,ex) :- agent(Agent0),agent(Agent1).
  evinst(meet(Agent0,Agent1),story) :- agent(Agent0),agent(Agent1).
  ifluent(perm(meet(Agent0,Agent1)), story) :- agent(Agent0),agent(Agent1).
  fluent(perm(meet(Agent0,Agent1)), story) :- agent(Agent0),agent(Agent1).
  event(viol(meet(Agent0,Agent1))) :- agent(Agent0),agent(Agent1).
  evtype(viol(meet(Agent0,Agent1)), story, viol) :- agent(Agent0),agent(Agent1).
  evinst(viol(meet(Agent0,Agent1)),story) :- agent(Agent0),agent(Agent1).
% Event: noDeadline (type: ex)
  event(noDeadline(Identity0)) :- identity(Identity0).
  evtype(noDeadline(Identity0),story,ex) :- identity(Identity0).
  evinst(noDeadline(Identity0),story) :- identity(Identity0).
  ifluent(perm(noDeadline(Identity0)), story) :- identity(Identity0).
  fluent(perm(noDeadline(Identity0)), story) :- identity(Identity0).
  event(viol(noDeadline(Identity0))) :- identity(Identity0).
  evtype(viol(noDeadline(Identity0)), story, viol) :- identity(Identity0).
  evinst(viol(noDeadline(Identity0)),story) :- identity(Identity0).
% Event: kill (type: ex)
  event(kill(Agent0,Agent1)) :- agent(Agent0),agent(Agent1).
  evtype(kill(Agent0,Agent1),story,ex) :- agent(Agent0),agent(Agent1).
  evinst(kill(Agent0,Agent1),story) :- agent(Agent0),agent(Agent1).
  ifluent(perm(kill(Agent0,Agent1)), story) :- agent(Agent0),agent(Agent1).
  fluent(perm(kill(Agent0,Agent1)), story) :- agent(Agent0),agent(Agent1).
  event(viol(kill(Agent0,Agent1))) :- agent(Agent0),agent(Agent1).
  evtype(viol(kill(Agent0,Agent1)), story, viol) :- agent(Agent0),agent(Agent1).
  evinst(viol(kill(Agent0,Agent1)),story) :- agent(Agent0),agent(Agent1).
%
% null event for unknown events
% Event: null (type: ex)
  event(null).
  evtype(null,story,ex).
  evinst(null,story).
  ifluent(perm(null), story).
  fluent(perm(null), story).
  event(viol(null)).
  evtype(viol(null),story,viol).
  evinst(viol(null),story).
% Institutional events
% Event: intGo (type: in)
  event(intGo(Agent0,PlaceName1)) :- agent(Agent0),placename(PlaceName1).
  evtype(intGo(Agent0,PlaceName1),story,inst) :- agent(Agent0),placename(PlaceName1).
  evinst(intGo(Agent0,PlaceName1),story) :- agent(Agent0),placename(PlaceName1).
  ifluent(pow(story,intGo(Agent0,PlaceName1)),story) :- agent(Agent0),placename(PlaceName1).
  ifluent(perm(intGo(Agent0,PlaceName1)),story) :- agent(Agent0),placename(PlaceName1).
  fluent(pow(story,intGo(Agent0,PlaceName1)),story) :- agent(Agent0),placename(PlaceName1).
  fluent(perm(intGo(Agent0,PlaceName1)),story) :- agent(Agent0),placename(PlaceName1).
  event(viol(intGo(Agent0,PlaceName1))) :- agent(Agent0),placename(PlaceName1).
  evtype(viol(intGo(Agent0,PlaceName1)),story,viol) :- agent(Agent0),placename(PlaceName1).
  evinst(viol(intGo(Agent0,PlaceName1)),story) :- agent(Agent0),placename(PlaceName1).
% Event: intHerosJourney (type: in)
  event(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  evtype(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4),story,inst) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  evinst(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4),story) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  ifluent(pow(story,intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)),story) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  ifluent(perm(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)),story) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  fluent(pow(story,intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)),story) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  fluent(perm(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)),story) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  event(viol(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4))) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  evtype(viol(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)),story,viol) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
  evinst(viol(intHerosJourney(Agent0,Agent1,Agent2,PlaceName3,PlaceName4)),story) :- agent(Agent0),agent(Agent1),agent(Agent2),placename(PlaceName3),placename(PlaceName4).
%
% Violation events
%
% Event: noViolation (type: in)
  event(noViolation(Identity0)) :- identity(Identity0).
  evtype(noViolation(Identity0),story,viol) :- identity(Identity0).
  evinst(noViolation(Identity0),story) :- identity(Identity0).
% Event: violAwayGoHero (type: in)
  event(violAwayGoHero) :- true.
  evtype(violAwayGoHero,story,viol) :- true.
  evinst(violAwayGoHero,story) :- true.
%
% Creation events
%
%
% Dissolution events
%
%
% dissolve events
%
%
% inertial fluents
%
ifluent(phase(Trope0,Phase1),story) :-
  trope(Trope0),phase(Phase1).
fluent(phase(Trope0,Phase1),story) :-
  trope(Trope0),phase(Phase1).

ifluent(place(PlaceName0,Place1),story) :-
  placename(PlaceName0),place(Place1).
fluent(place(PlaceName0,Place1),story) :-
  placename(PlaceName0),place(Place1).

ifluent(object(ObjectName0,Object1),story) :-
  objectname(ObjectName0),object(Object1).
fluent(object(ObjectName0,Object1),story) :-
  objectname(ObjectName0),object(Object1).

ifluent(role(Agent0,Role1),story) :-
  agent(Agent0),role(Role1).
fluent(role(Agent0,Role1),story) :-
  agent(Agent0),role(Role1).

ifluent(at(Agent0,Place1),story) :-
  agent(Agent0),place(Place1).
fluent(at(Agent0,Place1),story) :-
  agent(Agent0),place(Place1).

%
% noninertial fluents
%
%
% violation fluents (to be implemented)

%
% obligation fluents
%
oblfluent(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)), story) :-
   event(go(Agent0,PlaceName1)),
   event(go(Agent2,PlaceName3)),
   event(noViolation(Identity4)), agent(Agent0),placename(PlaceName1),agent(Agent2),placename(PlaceName3),identity(Identity4),inst(story).
ifluent(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)), story) :-
   event(go(Agent0,PlaceName1)),
   event(go(Agent2,PlaceName3)),
   event(noViolation(Identity4)), agent(Agent0),placename(PlaceName1),agent(Agent2),placename(PlaceName3),identity(Identity4),inst(story).
fluent(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)), story) :-
   event(go(Agent0,PlaceName1)),
   event(go(Agent2,PlaceName3)),
   event(noViolation(Identity4)), agent(Agent0),placename(PlaceName1),agent(Agent2),placename(PlaceName3),identity(Identity4),inst(story).
terminated(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)),story,I) :-
   event(go(Agent0,PlaceName1)), occurred(go(Agent0,PlaceName1),story,I),
   event(go(Agent2,PlaceName3)),
   holdsat(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)),story,I),
   event(noViolation(Identity4)), agent(Agent0),placename(PlaceName1),agent(Agent2),placename(PlaceName3),identity(Identity4),inst(story).
terminated(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)),story,I) :-
   event(go(Agent0,PlaceName1)), 
   event(go(Agent2,PlaceName3)), occurred(go(Agent2,PlaceName3),story,I),
   holdsat(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)),story,I),
   event(noViolation(Identity4)), agent(Agent0),placename(PlaceName1),agent(Agent2),placename(PlaceName3),identity(Identity4),inst(story).
occurred(noViolation(Identity4),story,I) :-
   event(go(Agent0,PlaceName1)), 
   event(go(Agent2,PlaceName3)), occurred(go(Agent2,PlaceName3),story,I),
   holdsat(obl(go(Agent0,PlaceName1),go(Agent2,PlaceName3),noViolation(Identity4)),story,I),
   event(noViolation(Identity4)), agent(Agent0),placename(PlaceName1),agent(Agent2),placename(PlaceName3),identity(Identity4),inst(story).
%
% -------------------------------PART 2-------------------------------
%
%
% generate rules
%
%
% Translation of go(R,T) generates intGo(R,T) if ['and', ['role', ['R', 'hero']], ['place', ['T', 'away']]] in 
occurred(intGo(R,T),story,I) :- occurred(go(R,T),story,I),
   holdsat(pow(story,intGo(R,T)),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(T,away),story,I),
   agent(R),
   placename(T),
   inst(story), instant(I).
%
% Translation of kill(R,S) generates intHerosJourney(R,S,T,U,V) if ['and', ['role', ['R', 'hero']], ['role', ['S', 'villain']]] in 
occurred(intHerosJourney(R,S,T,U,V),story,I) :- occurred(kill(R,S),story,I),
   holdsat(pow(story,intHerosJourney(R,S,T,U,V)),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(role(S,villain),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of go(R,V) generates intHerosJourney(R,S,T,U,V) if ['and', ['role', ['R', 'hero']], ['place', ['V', 'home']]] in 
occurred(intHerosJourney(R,S,T,U,V),story,I) :- occurred(go(R,V),story,I),
   holdsat(pow(story,intHerosJourney(R,S,T,U,V)),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(V,home),story,I),
   agent(R),
   placename(V),
   agent(S),
   placename(U),
   agent(T),
   inst(story), instant(I).
%
% Translation of meet(R,T) generates intHerosJourney(R,S,T,U,V) if ['and', ['role', ['R', 'hero']], ['role', ['T', 'dispatcher']]] in 
occurred(intHerosJourney(R,S,T,U,V),story,I) :- occurred(meet(R,T),story,I),
   holdsat(pow(story,intHerosJourney(R,S,T,U,V)),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(role(T,dispatcher),story,I),
   agent(R),
   agent(T),
   agent(S),
   placename(U),
   placename(V),
   inst(story), instant(I).
%
% initiate rules
%
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['phase', ['herosJourney', 'done']] if ['phase', ['herosJourney', 'phaseE']]
%
initiated(phase(herosJourney,done),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseE),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['phase', ['herosJourney', 'phaseE']] if ['and', ['and', ['phase', ['herosJourney', 'phaseD']], ['role', ['R', 'hero']]], ['place', ['V', 'home']]]
%
initiated(phase(herosJourney,phaseE),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseD),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(V,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['perm', ['go', ['R', 'V']]] if ['and', ['and', ['phase', ['herosJourney', 'phaseD']], ['role', ['R', 'hero']]], ['place', ['V', 'home']]]
%
initiated(perm(go(R,V)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseD),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(V,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['phase', ['herosJourney', 'phaseD']] if ['and', ['and', ['phase', ['herosJourney', 'phaseC']], ['role', ['R', 'hero']]], ['role', ['S', 'villain']]]
%
initiated(phase(herosJourney,phaseD),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseC),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(role(S,villain),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['perm', ['kill', ['R', 'S']]] if ['and', ['and', ['phase', ['herosJourney', 'phaseC']], ['role', ['R', 'hero']]], ['role', ['S', 'villain']]]
%
initiated(perm(kill(R,S)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseC),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(role(S,villain),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['phase', ['herosJourney', 'phaseC']] if ['and', ['and', ['and', ['and', ['phase', ['herosJourney', 'phaseB']], ['role', ['R', 'hero']]], ['place', ['U', 'away']]], ['role', ['S', 'villain']]], ['place', ['V', 'home']]]
%
initiated(phase(herosJourney,phaseC),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseB),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(U,away),story,I),
   holdsat(role(S,villain),story,I),
   holdsat(place(V,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['obl', [['go', ['R', 'U']], ['go', ['S', 'V']], ['noViolation', ['Identity']]]] if ['and', ['and', ['and', ['and', ['phase', ['herosJourney', 'phaseB']], ['role', ['R', 'hero']]], ['place', ['U', 'away']]], ['role', ['S', 'villain']]], ['place', ['V', 'home']]]
%
initiated(obl(go(R,U),go(S,V),noViolation(Identity)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseB),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(U,away),story,I),
   holdsat(role(S,villain),story,I),
   holdsat(place(V,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   identity(Identity),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['phase', ['herosJourney', 'phaseB']] if ['and', ['and', ['phase', ['herosJourney', 'phaseA']], ['role', ['R', 'hero']]], ['role', ['T', 'dispatcher']]]
%
initiated(phase(herosJourney,phaseB),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseA),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(role(T,dispatcher),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['perm', ['meet', ['R', 'T']]] if ['and', ['and', ['phase', ['herosJourney', 'phaseA']], ['role', ['R', 'hero']]], ['role', ['T', 'dispatcher']]]
%
initiated(perm(meet(R,T)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,phaseA),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(role(T,dispatcher),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['phase', ['herosJourney', 'phaseA']] if ['and', ['and', ['phase', ['herosJourney', 'inactive']], ['role', ['R', 'hero']]], ['place', ['V', 'home']]]
%
initiated(phase(herosJourney,phaseA),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,inactive),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(V,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) initiates ['perm', ['go', ['R', 'V']]] if ['and', ['and', ['phase', ['herosJourney', 'inactive']], ['role', ['R', 'hero']]], ['place', ['V', 'home']]]
%
initiated(perm(go(R,V)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I), inst(story),
   holdsat(phase(herosJourney,inactive),story,I),
   holdsat(role(R,hero),story,I),
   holdsat(place(V,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% terminate rules
%
%
% Translation of intGo(S,U) terminates ['obl', [['go', ['R', 'T']], ['go', ['S', 'U']], ['noViolation', ['Identity']]]] if ['and', ['and', ['and', ['role', ['R', 'hero']], ['place', ['T', 'away']]], ['role', ['S', 'villain']]], ['place', ['U', 'home']]]
%
terminated(obl(go(R,T),go(S,U),noViolation(Identity)),story,I) :-
   occurred(intGo(S,U),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(role(R,hero),story,I),
   holdsat(place(T,away),story,I),
   holdsat(role(S,villain),story,I),
   holdsat(place(U,home),story,I),
   agent(S),
   agent(R),
   placename(U),
   placename(T),
   identity(Identity),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'done']] if ['phase', ['herosJourney', 'done']]
%
terminated(phase(herosJourney,done),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,done),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'phaseE']] if ['phase', ['herosJourney', 'phaseE']]
%
terminated(phase(herosJourney,phaseE),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseE),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['perm', ['go', ['R', 'V']]] if ['phase', ['herosJourney', 'phaseE']]
%
terminated(perm(go(R,V)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseE),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'phaseD']] if ['phase', ['herosJourney', 'phaseD']]
%
terminated(phase(herosJourney,phaseD),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseD),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['perm', ['kill', ['R', 'S']]] if ['phase', ['herosJourney', 'phaseD']]
%
terminated(perm(kill(R,S)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseD),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'phaseC']] if ['phase', ['herosJourney', 'phaseC']]
%
terminated(phase(herosJourney,phaseC),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseC),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['obl', [['go', ['R', 'U']], ['go', ['S', 'V']], ['noViolation', ['Identity']]]] if ['phase', ['herosJourney', 'phaseC']]
%
terminated(obl(go(R,U),go(S,V),noViolation(Identity)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseC),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   identity(Identity),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'phaseB']] if ['phase', ['herosJourney', 'phaseB']]
%
terminated(phase(herosJourney,phaseB),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseB),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['perm', ['meet', ['R', 'T']]] if ['phase', ['herosJourney', 'phaseB']]
%
terminated(perm(meet(R,T)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseB),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'phaseA']] if ['phase', ['herosJourney', 'phaseA']]
%
terminated(phase(herosJourney,phaseA),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseA),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['perm', ['go', ['R', 'V']]] if ['phase', ['herosJourney', 'phaseA']]
%
terminated(perm(go(R,V)),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,phaseA),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% Translation of intHerosJourney(R,S,T,U,V) terminates ['phase', ['herosJourney', 'inactive']] if ['phase', ['herosJourney', 'inactive']]
%
terminated(phase(herosJourney,inactive),story,I) :-
   occurred(intHerosJourney(R,S,T,U,V),story,I),
   holdsat(live(story),story,I),inst(story),
   holdsat(phase(herosJourney,inactive),story,I),
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   inst(story), instant(I).
%
% noninertial rules
%
%
% -------------------------------PART 3-------------------------------
%
%
% initially
%
% no creation event
holdsat(live(story),story,I) :- start(I), inst(story).
holdsat(perm(null),story,I) :- start(I), inst(story).
% initially: perm(go(R,V))
% condition: role(R,hero) and place(V,home)
holdsat(perm(go(R,V)),story,I) :-
   agent(R),
   placename(V),
   holdsat(role(R,hero),story,I),
   holdsat(place(V,home),story,I),
   inst(story), start(I).
% initially: pow(story,intHerosJourney(R,S,T,U,V))
% condition: R!=S and S!=T and T!=U and U!=V
holdsat(pow(story,intHerosJourney(R,S,T,U,V)),story,I) :-
   agent(S),
   agent(R),
   placename(U),
   agent(T),
   placename(V),
   R!=S,
   S!=T,
   T!=U,
   U!=V,
   inst(story), start(I).
% initially: pow(story,intGo(S,U))
holdsat(pow(story,intGo(S,U)),story,I) :-
   agent(S),
   placename(U),
   inst(story), start(I).
% initially: phase(herosJourney,phaseA)
holdsat(phase(herosJourney,phaseA),story,I) :-
   inst(story), start(I).
% initially: role(lukeSkywalker,hero)
holdsat(role(lukeSkywalker,hero),story,I) :-
   inst(story), start(I).
% initially: role(professorMoriarty,villain)
holdsat(role(professorMoriarty,villain),story,I) :-
   inst(story), start(I).
% initially: role(commissionerGordon,dispatcher)
holdsat(role(commissionerGordon,dispatcher),story,I) :-
   inst(story), start(I).
% initially: place(tatooine,home)
holdsat(place(tatooine,home),story,I) :-
   inst(story), start(I).
% initially: place(jungle,away)
holdsat(place(jungle,away),story,I) :-
   inst(story), start(I).
%
% -------------------------------GROUNDING-------------------------------
%
% PlaceName
#program placename(l).
placename(l).

% ObjectName
#program objectname(l).
objectname(l).

% Object
#program object(l).
object(l).

% Agent
#program agent(l).
agent(l).

% Place
#program place(l).
place(l).

% Phase
#program phase(l).
phase(l).

% Role
#program role(l).
role(l).

% Trope
#program trope(l).
trope(l).

% Identity
#program identity(l).
identity(l).

%
% End of file
%
