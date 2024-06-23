# define N 5
# define WAIT(BOOL_EXPR) BOOL_EXPR


# define de_ns (DE_GREEN && NS_GREEN)
# define de_sd (DE_GREEN && SD_GREEN)
# define dn_ns (DN_GREEN && NS_GREEN)
# define sd_wn (SD_GREEN && WN_GREEN)
# define sd_dn (SD_GREEN && DN_GREEN)
# define sd_ns (SD_GREEN && NS_GREEN)
# define wn_de (WN_GREEN && DE_GREEN)
# define ns_wn (NS_GREEN && WN_GREEN)

# define SD_GREEN (SD_light == GREEN)
# define NS_GREEN (NS_light == GREEN)
# define WN_GREEN (WN_light == GREEN)
# define DE_GREEN (DE_light == GREEN)
# define DN_GREEN (DN_light == GREEN)

ltl safety { [] ! (de_ns || de_sd || dn_ns || sd_wn || sd_dn|| sd_ns || wn_de || ns_wn) }


# define sd_car (SD_req && SD_light == 0)
# define sd_green (SD_light == 1)

# define wn_car (WN_req && WN_light == 0)
# define wn_green (WN_light == 1)

# define dn_car (DN_req && DN_light == 0)
# define dn_green (DN_light == 1)

# define de_car (DE_req && DE_light == 0)
# define de_green (DE_light == 1)

# define ns_car (NS_req && NS_light == 0)
# define ns_green (NS_light == 1)

ltl liveness { [] ( (sd_car -> <> sd_green) && (wn_car -> <> wn_green) && (dn_car -> <> dn_green) && (de_car -> <> de_green) && (ns_car -> <> ns_green) ) }


# define sd_req (SD_req == 1)
# define sd_green (SD_light == 1)
# define sd_fair (SD_req && SD_light == 1)

# define wn_req (WN_req == 1)
# define wn_green (WN_light == 1)
# define wn_fair (WN_req && WN_light == 1)

# define dn_req (DN_req == 1)
# define dn_green (DN_light == 1)
# define dn_fair (DN_req && DN_light == 1)

# define de_req (DE_req == 1)
# define de_green (DE_light == 1)
# define de_fair (DE_req && DE_light == 1)

# define ns_req (NS_req == 1)
# define ns_green (NS_light == 1)
# define ns_fair (NS_req && NS_light == 1)

ltl fair { [] <> ! (sd_fair) && [] <> ! (wn_fair) && [] <> ! (dn_fair) && [] <> ! (de_fair) && [] <> !  (ns_fair) }
ltl fairness { []<>! (sd_req && sd_green) && []<>! (wn_req && wn_green) && []<>! (dn_req && dn_green) && []<>! (de_req && de_green) && []<>! (ns_req && ns_green) }


typedef traf_light {
  byte count;
  byte blocked_count;
  byte blocked[N];
  byte j;
}

inline down(semaphore, i) {
    atomic {
        if
        :: (semaphore.count > 0) -> semaphore.count--;
        :: else ->
            semaphore.blocked_count++;
            semaphore.blocked[i] = semaphore.blocked_count;
            WAIT(semaphore.blocked[i] == 0);
        fi;
    }
}

inline up(semaphore, i) {
    atomic {
        if
        :: (semaphore.blocked_count == 0) -> semaphore.count++;
        :: else ->
            semaphore.j = 0;
            do
            :: (semaphore.j < N && semaphore.blocked[semaphore.j] > 0) ->
                semaphore.blocked[semaphore.j]--;
                semaphore.j++;
            :: (semaphore.j < N && !semaphore.blocked[semaphore.j] > 0) ->
                semaphore.j++;
            :: else -> break;
            od;
            semaphore.blocked_count--;
        fi;
    }
}

traf_light wait_and_lock;

bool SD_req = false;
bool WN_req = false;
bool DN_req = false;
bool DE_req = false;
bool NS_req = false;

bool SD_lock = false;
bool WN_lock = false;
bool DN_lock = false;
bool DE_lock = false;
bool NS_lock = false;

mtype = {GREEN, RED};
int SD_light = RED;
int WN_light = RED;
int DN_light = RED;
int DE_light = RED;
int NS_light = RED;

proctype SD(int i) {
  do
  :: (SD_req) ->
      down(wait_and_lock, i);
      WAIT(!WN_lock && !DN_lock && !DE_lock && !NS_lock);
      SD_lock = true;
      up(wait_and_lock, i);

      atomic {
          SD_light = GREEN;
          printf("MSC: SD - GREEN\n");
          SD_req = false;
      }
      WAIT(!SD_req);
      atomic {
          SD_light = RED;
          printf("MSC: SD - RED\n");
      }
      SD_lock = false;
  od;
}

proctype WN(int i) {
  do
  :: (WN_req) ->
      down(wait_and_lock, i);
      WAIT(!SD_lock && !DE_lock && !NS_lock);
      WN_lock = true;
      up(wait_and_lock, i);

      atomic {
          WN_light = GREEN;
          printf("MSC: WN - GREEN\n");
          WN_req = false;
      }
      WAIT(!WN_req);
      atomic {
          WN_light = RED;
          printf("MSC: WN - RED\n");
      }
      WN_lock = false;
  od;
}

proctype DN(int i) {
  do
  :: (DN_req) ->
      down(wait_and_lock, i);
      WAIT(!SD_lock && !NS_lock);
      DN_lock = true;
      up(wait_and_lock, i);

      atomic {
          DN_light = GREEN;
          printf("MSC: DN - GREEN\n");
          DN_req = false;
      }
      WAIT(!DN_req);
      atomic {
          DN_light = RED;
          printf("MSC: DN - RED\n");
      }
      DN_lock = false;
  od;
}

proctype DE(int i) {
  do
  :: (DE_req) ->
      down(wait_and_lock, i);
      WAIT(!SD_lock && !WN_lock && !NS_lock);
      DE_lock = true;
      up(wait_and_lock, i);

      atomic {
          DE_light = GREEN;
          printf("MSC: DE - GREEN\n");
          DE_req = false;
      }
      WAIT(!DE_req);
      atomic {
          DE_light = RED;
          printf("MSC: DE - RED\n");
      }
      DE_lock = false;
  od;
}

proctype NS(int i) {
  do
  :: (NS_req) ->
      down(wait_and_lock, i);
      WAIT(!SD_lock && !WN_lock && !DN_lock && !DE_lock);
      NS_lock = true;
      up(wait_and_lock, i);

      atomic {
          NS_light = GREEN;
          printf("MSC: NS - GREEN\n");
          NS_req = false;
      }
      WAIT(!NS_req);
      atomic {
          NS_light = RED;
          printf("MSC: NS - RED\n");
      }
      NS_lock = false;
  od;
}

proctype traf_emulator() {
  do
  :: (!SD_req) -> 
      SD_req = true;
  :: (!WN_req) -> 
      WN_req = true;
  :: (!DN_req) -> 
      DN_req = true;
  :: (!DE_req) -> 
      DE_req = true;
  :: (!NS_req) -> 
      NS_req = true;

  :: (SD_req && !SD_lock) -> 
      SD_req = false;
  :: (WN_req && !WN_lock) -> 
      WN_req = false;
  :: (DN_req && !DN_lock) -> 
      DN_req = false;
  :: (DE_req && !DE_lock) -> 
      DE_req = false;
  :: (NS_req && !NS_lock) -> 
      NS_req = false;
  od;
}

init {
  int j;
  wait_and_lock.count = 1;
  atomic {
    run traf_emulator();
    run SD(0);
    run WN(1);
    run DN(2);
    run DE(3);
    run NS(4);
  }
}
