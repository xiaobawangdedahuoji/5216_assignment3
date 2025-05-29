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
