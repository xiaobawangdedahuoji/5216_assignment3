%%%% Service and Maintenance scheduling
int: endtime;                   % latest time to be scheduled
set of int: TIME = 0..endtime;
enum SERVICE;                   % services to be scheduled
array[SERVICE] of TIME: start;  % start time of service
array[SERVICE] of TIME: end;    % end time of service
enum STYPE;
array[SERVICE] of STYPE: stype; % type of each service

enum TRUCK;                      % truck 
TRUCK: dtruck;                   % dummy truck
enum TTYPE = { SML, MED, LRG, DUMMY };  % truck type
array[TRUCK] of TTYPE: ttype;    % type of each truck
array[TRUCK] of int: prework;    % units of work since last major maintenance
constraint assert(forall(t in TRUCK)(ttype[t] = DUMMY <-> t = dtruck),"dummy type only for dtruck\n");
array[TTYPE] of int: maxsty;     % max service types for each truck type

enum MAINTYPE = { NO, SH, LG, MJ }; % NO means no maintenance
array[MAINTYPE] of int: maintdur; % duration of maintenance
array[MAINTYPE] of int: maxsep;   % max elapsed time since last maint of this type or higher
constraint assert(maintdur[NO] = 0 /\ maxsep[NO] = 0, "rules for empty maintenance\n");

int: minwork;                   % minimal percentage of time each truck that works is working
int: minservice;                % minimal percentage of services performed

int: majorwork;                 % amount of work allowed before major maintenance required


array[SERVICE] of var TRUCK: truck; % which truck takes each service: dtruck if none

int: maxmaint;
set of int: MAINT = 1..maxmaint;
array[TRUCK,MAINT] of var MAINTYPE: mt; % maintenance for each truck NO means not used.
array[TRUCK,MAINT] of var TIME: ms;     % maintenance start time for each truck

include "globals.mzn";

% ===== extra constraint about Variable Bounds =====
constraint forall(t in TRUCK, m in MAINT)(
    ms[t, m] + maintdur[mt[t, m]] <= endtime
);

% ===== Stage A: Assigning Services =====
% the same truck cannot overlap in time (except dummy truck DD)
array[SERVICE] of int: service_duration = [end[s] - start[s] | s in SERVICE];
constraint forall(t in TRUCK where t != dtruck)(
    cumulative(
        [start[s] | s in SERVICE] ++ [ms[t,m] | m in MAINT],
        [service_duration[s] | s in SERVICE] ++ [maintdur[mt[t,m]] | m in MAINT],
        [bool2int(truck[s] = t) | s in SERVICE] ++ [bool2int(mt[t,m] != NO) | m in MAINT],
        1
    )
);

% %%%%% symmetry breaking for same services: same start/end => enforce truck order (SPECIAL#1) %%%%%
constraint forall(i, j in SERVICE where i < j /\ start[i] = start[j] /\ end[i] = end[j])(
      truck[i] <= truck[j]
);


% ===== Stage B: Truck Usage, Service Guarantee =====
% total work time of each truck
array[TRUCK] of var 0..endtime: truck_worktime;
constraint forall(t in TRUCK)(
    truck_worktime[t] = sum(s in SERVICE)(
        bool2int(truck[s] = t) * service_duration[s]
    )
);         
% B1 the work time of each truck must meet the threshold - minwork
constraint forall(t in TRUCK where t != dtruck)(
                 (truck_worktime[t] > 0) -> (truck_worktime[t] * 100 >= minwork * endtime)
);
% the num of completed services
var 0..card(SERVICE): services_completed;
constraint
  services_completed =
    sum(s in SERVICE)(bool2int(truck[s] != dtruck)); 
% B2 total completed services must meet the threshold - minservice
constraint services_completed * 100 >= minservice * card(SERVICE);

% ===== Stage C: Work Types =====
% record whether a truck has performed any type of service
array[TRUCK, STYPE] of var bool: truck_stype_done;
constraint forall(t in TRUCK where t != dtruck)(
              forall(st in STYPE)(
                truck_stype_done[t, st] = exists(s in SERVICE where truck[s] = t)(stype[s] = st)
              )     
);

% each truck (except the dummy one) can be arranged services of at most maxsty[ttype[t]] different types
constraint if card(STYPE) > 1 then
    forall(t in TRUCK where t != dtruck)(
        sum(st in STYPE)(truck_stype_done[t, st]) <= maxsty[ttype[t]]
    )
else
    true
endif;

                 
% ===== Stage D: Maintenance =====
% D0 - dummy truck do not need maintenance
constraint forall(m in MAINT)( mt[dtruck,m] = NO );

% D1 - truck not use don't need maintenance
constraint forall(t in TRUCK where t != dtruck) (
                  truck_worktime[t] = 0 -> forall(m in MAINT)(mt[t,m] = NO /\ ms[t, m] = 0)
);
               
% D2 - make sure all the NO maintenances appear at the end of the list for each truck
constraint forall(t in TRUCK where t != dtruck, m in 1..maxmaint - 1)(
                  mt[t, m] = NO -> mt[t, m + 1] = NO    
);

% D3 - make sure other maintenances appear in order of increasing start time
constraint forall(t in TRUCK where t != dtruck, m in 1..maxmaint-1)(
    (mt[t,m] != NO /\ mt[t,m+1] != NO) -> 
    (ms[t,m] + maintdur[mt[t,m]] <= ms[t,m+1] /\ ms[t,m] <= ms[t, m+1])
);

% D4 - make sure maintenance and service time don't overlap === [remove, covered by cumulative from Stage A]
% constraint forall(t in TRUCK where t != dtruck, m in MAINT, s in SERVICE)(
%                  (truck[s] = t /\ mt[t, m] != NO) -> 
%                  (start[s] + service_duration[s] <= ms[t, m] \/
%                   ms[t, m] + maintdur[mt[t, m]] <= start[s])
% );

% D5 - there must be a SH/LG or MJ maintenance within maxsep[SH] of the start
% way 1
constraint forall(t in TRUCK where t != dtruck /\ truck_worktime[t] > 0)(
                  exists(m in MAINT) (mt[t,m] != NO /\ ms[t,m] <= maxsep[SH])
);

% way 2: maintain a list for each truck containing all maintenance tasks that can possibly start within maxsep[SH]
% array[TRUCK] of var set of MAINT: possible_maint = 
%   [ {m | m in MAINT where mt[t, m] != NO /\ ms[t, m] <= maxsep[SH]} | t in TRUCK ];
% constraint forall(t in TRUCK where t != dtruck /\ truck_worktime[t] > 0) (
%                   card(possible_maint[t]) > 0
% );

% D6 - There must be a LG or MJ maintenance within maxsep[LG] of the start of the schedule
constraint forall(t in TRUCK  where t != dtruck /\ truck_worktime[t] > 0) (
                  exists(m in MAINT) (mt[t, m] in {LG, MJ} /\ ms[t, m] <= maxsep[LG])
);

% D7 - make sure there is another SH/LG or MJ after every SH/LG or MJ within maxsep[SH]
% way 1
constraint forall(t in TRUCK where t != dtruck, m1 in MAINT where mt[t,m1] != NO)(
    ms[t,m1] + maintdur[mt[t,m1]] + maxsep[SH] >= endtime 
    \/ exists(m2 in MAINT where m2>m1)(
         mt[t,m2] != NO /\ ms[t,m2] <= ms[t,m1] + maintdur[mt[t,m1]] + maxsep[SH]
       )
);

% ======== way 2 START =========
% array[TRUCK, MAINT] of var TIME: end_time_maint;  % the end time for each maintenance task:
% constraint forall(t in TRUCK, m in MAINT)(end_time_maint[t,m] = ms[t,m] + maintdur[mt[t,m]]);

% % the set of possible next maintenances m2 for each truck t and each maintenance task m1
% array[TRUCK, MAINT] of var set of MAINT: next_maint = 
%   array2d(TRUCK, MAINT,
%     [ { m2 | m2 in MAINT 
%         where 
%              m2 > m1 /\ mt[t,m2] != NO /\ ms[t,m2] 
%              <= end_time_maint[t,m1] + maxsep[SH] 
%       }
%       | t in TRUCK, m1 in MAINT
%     ]
%   );

% % either the task ends late enough (> endtime),
% % or there exists at least one suitable follow-up task m2 in the next_maint set
% constraint forall(t in TRUCK where t != dtruck, m1 in MAINT where mt[t,m1] != NO)(
%                   end_time_maint[t,m1] + maxsep[SH] >= endtime \/
%                   card(next_maint[t, m1]) > 0
% );
% =========== way 2 END ===========


% D8 - make sure there is another LG or MJ after every LG or MJ within maxsep[LG]
% way 1
constraint forall(t in TRUCK where t != dtruck, m1 in MAINT where mt[t,m1] in {LG,MJ})(
    ms[t,m1] + maintdur[mt[t,m1]] + maxsep[LG] >= endtime
    \/ exists(m2 in MAINT where m2>m1)(
         mt[t,m2] in {LG,MJ} /\ ms[t,m2] <= ms[t,m1] + maintdur[mt[t,m1]] + maxsep[LG]
       )
);

% ======== way 2 START =========
% array[TRUCK, MAINT] of var TIME: end_time_maint2;  % the end time for each maintenance task(LG or MJ):
% constraint forall(t in TRUCK, m in MAINT where mt[t, m] in {LG, MJ})(end_time_maint2[t,m] = ms[t,m] + maintdur[mt[t,m]]);

% the set of possible next maintenances m2 for each truck t and each maintenance task m1
% array[TRUCK, MAINT] of var set of MAINT: next_maint2 = 
%   array2d(TRUCK, MAINT,
%     [ { m2 | m2 in MAINT 
%         where 
%              mt[t, m1] in {LG, MJ} /\ mt[t, m2] in {LG, MJ} /\
%              m2 > m1 /\ mt[t,m2] != NO /\ ms[t,m2] 
%              <= end_time_maint2[t,m1] + maxsep[LG] 
%       }
%       | t in TRUCK, m1 in MAINT 
%     ]
%   );

% % either the task ends late enough (> endtime),
% % or there exists at least one suitable follow-up task m2 in the next_maint2 set
% constraint forall(t in TRUCK where t != dtruck, m1 in MAINT where mt[t, m1] in {LG, MJ})(
%                   end_time_maint2[t,m1] + maxsep[LG] >= endtime \/
%                   card(next_maint2[t, m1]) > 0
% );
% =========== way 2 END ===========


% ===== Stage E: Objective =====
% store the number of maintenance tasks for each time t
array[0..endtime - 1] of var 0..card(TRUCK) * maxmaint: num_maint;
constraint
  forall(t in 0..endtime - 1) (
    num_maint[t] =
      sum(tk in TRUCK, m in MAINT where mt[tk, m] != NO)(
        bool2int(mt[tk, m] != NO /\ ms[tk, m] <= t /\ t < ms[tk, m] + maintdur[mt[tk, m]])
      )
  );

int: max_total_service = sum(service_duration);

% total duration of services
var 0..max_total_service: totalService = 
    sum(s in SERVICE)(bool2int(truck[s] != dtruck) * service_duration[s]);

% total maintenance load
var 0..card(TRUCK)*maxmaint*card(TRUCK)*maxmaint*endtime: totalLoad = 
    sum(t in 0..endtime-1)(num_maint[t] * num_maint[t]);

% assume a weight
int: service_time_max = card(SERVICE) * endtime;
int: weight = service_time_max + 1;


% ==== Stage F: Major Maintenance =====
constraint forall(t in TRUCK where t != dtruck)(
    let {
        % whether the current truck has MJ
        var bool: has_mj = exists(m in MAINT)(mt[t,m] = MJ);
        % the start time of the first MJ service
        var TIME: first_mj_start = 
            if has_mj 
            then min([ms[t,m] | m in MAINT where mt[t,m] = MJ]) 
            else endtime endif;
        % the end time of the last MJ service
        var TIME: last_mj_end = 
            if has_mj 
            then max([ms[t,m] + maintdur[MJ] | m in MAINT where mt[t,m] = MJ]) 
            else 0 endif
    } in
    (
       if has_mj 
       then
          % total service time before the first MJ
          sum(s in SERVICE where truck[s] = t /\ start[s] < first_mj_start)(service_duration[s]) 
              + prework[t] <= majorwork
       else
          sum(s in SERVICE where truck[s] = t)(service_duration[s]) 
              + prework[t] <= majorwork
       endif
    )
    /\
    (
      if has_mj 
      then
          % total service time after the last MJ
          sum(s in SERVICE where truck[s] = t /\ start[s] >= last_mj_end)(service_duration[s]) <= majorwork
      else
          true
      endif
    )
    /\
      forall(m1 in MAINT where mt[t,m1] = MJ)(
          let {
              % whether the truck has another MJ
              var bool: has_next_mj = exists(m2 in m1+1..maxmaint)(mt[t,m2] = MJ),
              % anthoer MJ's start time
              var TIME: next_mj_start = 
                  if has_next_mj 
                  then min([ms[t,m2] | m2 in m1+1..maxmaint where mt[t,m2] = MJ]) 
                  else endtime endif
          } in
          % total service time between any two MJs
          sum(s in SERVICE where truck[s] = t /\ 
              ms[t,m1] + maintdur[MJ] <= start[s] /\ 
              start[s] < next_mj_start)
              (service_duration[s]) <= majorwork
    )
);

% ===== extra constraints for eliminate symmetry =====


% ===== extra constraints for pruning =====
array[TRUCK] of var 0..maxmaint: num_maint_tasks;
constraint forall(t in TRUCK)(
    num_maint_tasks[t] = sum(m in MAINT)(bool2int(mt[t,m] != NO))
);
constraint sum(t in TRUCK where t != dtruck)(num_maint_tasks[t]) <= card(TRUCK) * maxmaint;


% ====================== SOLVE ============================
solve minimize weight * totalLoad - totalService;
% solve minimize totalLoad;

% constraint totalLoad = 16 \/ totalLoad <= 9;
% constraint totalService = 25;

% output [
%     "mt: ", show(mt), "\n",
%     "ms: ", show(ms), "\n",
%     "truck: ", show(truck), "\n",
%     "num_maint: ", show(num_maint), "\n",
%     "totalLoad: ", show(totalLoad), " totalService: ", show(totalService)
% ];
