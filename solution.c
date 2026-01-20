#include <stdio.h> // for I/O and all that stuff
#include <stdlib.h> // std lib as it says
#include <string.h> // strings
#include <unistd.h>
#include <sys/ipc.h> // sys comm
#include <sys/msg.h> // msg comm
#include <sys/shm.h> // shared mem
#include <pthread.h> // threads (not used but allowed)
#include <limits.h> // limits - INT MAx and all
#include <errno.h>

// What was mentioned in Dipanjan sir's PDF
#define MAX_TRUCKS 250
#define TRUCK_MAX_CAP 20
#define MAX_NEW_REQUESTS 50
#define MAX_TOTAL_PACKAGES 5000

#define MAX_GRID 500 // add'nal
#define AUTH_PKG_LIMIT 4
// Mandatory 
typedef struct PackageRequest {
    int packageId;
    int pickup_x;
    int pickup_y;
    int dropoff_x;
    int dropoff_y;
    int arrival_turn;
    int expiry_turn;
} PackageRequest;
typedef struct MainSharedMemory {
    char authStrings[MAX_TRUCKS][TRUCK_MAX_CAP + 1];
    char truckMovementInstructions[MAX_TRUCKS];
    int pickUpCommands[MAX_TRUCKS];
    int dropOffCommands[MAX_TRUCKS];
    int truckPositions[MAX_TRUCKS][2]; // [i][0] = x, [i][1] = y for truck i
    int truckPackageCount[MAX_TRUCKS];
    int truckTurnsInToll[MAX_TRUCKS];
    PackageRequest newPackageRequests[MAX_NEW_REQUESTS];
    int packageLocations[MAX_TOTAL_PACKAGES][2];
} MainSharedMemory;
typedef struct TurnChangeResponse {
    long mtype;
    int turnNumber;
    int newPackageRequestCount;
    int errorOccurred;
    int finished;
} TurnChangeResponse;
typedef struct TurnReadyRequest {
    long mtype;
} TurnReadyRequest;
typedef struct SolverRequest {
    long mtype;
    int truckNumber;
    char authStringGuess[TRUCK_MAX_CAP + 1];
} SolverRequest;
typedef struct SolverResponse {
    long mtype;
    int guessIsCorrect;
} SolverResponse;

// Globals vars
static int bigN_rows, totalDepots, solverCountS, startingTrucksT, mapBoundB;
static int shmKeyCentral, mainBellKey;
static int solverPagersKeys[MAX_GRID];
static MainSharedMemory *centralPerkBoard = NULL;
static int centralBellQueue = -1, centralShmId = -1;
static int guntherPager[MAX_GRID];

typedef struct { //Addnal struct 
    int id;
    int pickup_x, pickup_y;
    int dropoff_x, dropoff_y;
    int expiry_turn;
    int status; // 0 waiting, 1 picked, 2 delivered
    int truck_id;
} PackageInfo;
static PackageInfo packagesFanMail[MAX_TOTAL_PACKAGES];
static int fanMailCount = 0;
static int seasonEpisode = 1;

// Manhattan Variant
static inline int joeyCountBlocksLikePizzaSlices(int x1, int y1, int x2, int y2) {
    return abs(x1 - x2) + abs(y1 - y2);
}
// Determine the dirn
static inline char phoebeHumsAStep(int fromX, int fromY, int toX, int toY) {
    if (fromX < toX) return 'r';
    if (fromX > toX) return 'l';
    if (fromY < toY) return 'd';
    if (fromY > toY) return 'u';
    return 's';
}

//Input parsing and IPC attach
static void chandlerReadStageDirections(void) {
    FILE *fp = fopen("input.txt", "r");
    if (!fp) {
        exit(1);
    }

    if (fscanf(fp, "%d %d %d %d %d",
               &bigN_rows, &totalDepots, &solverCountS, &startingTrucksT, &mapBoundB) != 5) {
        fclose(fp);
        exit(1);
    }

    if (fscanf(fp, "%d", &shmKeyCentral) != 1) { fclose(fp); exit(1); }
    if (fscanf(fp, "%d", &mainBellKey) != 1) { fclose(fp); exit(1); }

    if (solverCountS < 0 || solverCountS > MAX_GRID) {
        fclose(fp);
        exit(1);
    }

    for (int i = 0; i < solverCountS; ++i) {
        if (fscanf(fp, "%d", &solverPagersKeys[i]) != 1) {
            fclose(fp);
            exit(1);
        }
    }
    fclose(fp);
}

static int monicaAttachQueue(int key) {
    int q = msgget(key, 0666);
    if (q == -1) {
        exit(1);
    }
    return q;
}

static MainSharedMemory* monicaAttachShm(int key) {
    int id = shmget(key, sizeof(MainSharedMemory), 0666);
    if (id == -1) {
        exit(1);
    }
    void *p = shmat(id, NULL, 0);
    if (p == (void*)-1) {
        exit(1);
    }
    centralShmId = id;
    return (MainSharedMemory*)p;
}

static void monicaPrepTheCentralPerkIPC(void) {
    centralBellQueue = monicaAttachQueue(mainBellKey);
    for (int i = 0; i < solverCountS; ++i) guntherPager[i] = monicaAttachQueue(solverPagersKeys[i]);
    centralPerkBoard = monicaAttachShm(shmKeyCentral);
}
// Solver message helper
static int solver_select_truck(int pager, int truckId) {
    SolverRequest sel;
    sel.mtype = 2;
    sel.truckNumber = truckId;
    sel.authStringGuess[0] = '\0';
    if (msgsnd(guntherPager[pager], &sel, sizeof(sel) - sizeof(long), 0) != 0) {
        return -1;
    }
    return 0;
}

static int solver_try_guess_and_wait(int pager, int truckId, const char *guess) {
    SolverRequest req;
    req.mtype = 3;
    req.truckNumber = truckId;
    strncpy(req.authStringGuess, guess, TRUCK_MAX_CAP);
    req.authStringGuess[TRUCK_MAX_CAP] = '\0';

    if (msgsnd(guntherPager[pager], &req, sizeof(req) - sizeof(long), 0) != 0) {
        return -1;
    }
    SolverResponse resp;
    if (msgrcv(guntherPager[pager], &resp, sizeof(resp) - sizeof(long), 4, 0) < 0) {
        return -1;
    }
    return resp.guessIsCorrect ? 1 : 0;
}
// Rachel brute force logic 
static void rachelGuessTheSecretWord(int truckId, int packageCountOnTruck, char *outBuf) {
    if (packageCountOnTruck <= 0) { outBuf[0] = '\0'; return; }
    if (packageCountOnTruck > AUTH_PKG_LIMIT) packageCountOnTruck = AUTH_PKG_LIMIT;
    if (solverCountS <= 0) { outBuf[0] = '\0'; return; }

    int pager = truckId % solverCountS;
    if (solver_select_truck(pager, truckId) != 0) { outBuf[0] = '\0'; return; }

    static const char moves[] = { 'u', 'd', 'l', 'r' };
    char guess[TRUCK_MAX_CAP + 1];

    int total = 1 << (2 * packageCountOnTruck); // 4^k
    for (int code = 0; code < total; ++code) {
        int tmp = code;
        for (int i = 0; i < packageCountOnTruck; ++i) {
            guess[i] = moves[tmp & 3];
            tmp >>= 2;
        }
        guess[packageCountOnTruck] = '\0';

        int r = solver_try_guess_and_wait(pager, truckId, guess);
        if (r == 1) { strcpy(outBuf, guess); return; }
        if (r == -1) { outBuf[0] = '\0'; return; } 
    }
    outBuf[0] = '\0';
}

//Urgency scoring 
static inline int rachelDropScore(int tx, int ty, const PackageInfo *p, int nowTurn) {
    int dist = joeyCountBlocksLikePizzaSlices(tx, ty, p->dropoff_x, p->dropoff_y);
    int timeLeft = p->expiry_turn - nowTurn;
    if (timeLeft < 0) timeLeft = 0;
    return 3 * dist + timeLeft;
}
static inline int rachelPickupUrgency(int nowTurn, int expiry) {
    int tl = expiry - nowTurn;
    return (tl > 0) ? tl : (1000 - tl);
}

// Ingest new package requests
static void rossIngestNewPackages(const TurnChangeResponse *note) {
    if (note->newPackageRequestCount <= 0) return;
    PackageRequest *src = centralPerkBoard->newPackageRequests;
    int n = note->newPackageRequestCount;
    for (int k = 0; k < n; ++k) {
        if (fanMailCount >= MAX_TOTAL_PACKAGES) {
            /* original code appended without guard; we preserve behaviour by
               skipping extra entries to avoid overflow. */
            continue;
        }
        PackageInfo *slot = &packagesFanMail[fanMailCount++];
        slot->id = src[k].packageId;
        slot->pickup_x = src[k].pickup_x;
        slot->pickup_y = src[k].pickup_y;
        slot->dropoff_x = src[k].dropoff_x;
        slot->dropoff_y = src[k].dropoff_y;
        slot->expiry_turn = src[k].expiry_turn;
        slot->status = 0;
        slot->truck_id = -1;
    }
}
// Clear commands 
static void rossClearTruckCommands(void) {
    for (int t = 0; t < totalDepots; ++t) {
        centralPerkBoard->pickUpCommands[t] = -1;
        centralPerkBoard->dropOffCommands[t] = -1;
        centralPerkBoard->truckMovementInstructions[t] = 's';
        centralPerkBoard->authStrings[t][0] = '\0';
    }
}
//Per truck decision
static void rossPickDropMoveForTruck(int t) {
    int tx = centralPerkBoard->truckPositions[t][0];
    int ty = centralPerkBoard->truckPositions[t][1];
    int carry = centralPerkBoard->truckPackageCount[t];

    if (centralPerkBoard->truckTurnsInToll[t] > 0) return;

    //Best drop among carried 
    int bestDropIdx = -1;
    int bestDropSc = INT_MAX;
    for (int i = 0; i < fanMailCount; ++i) {
        PackageInfo *p = &packagesFanMail[i];
        if (p->status == 1 && p->truck_id == t) {
            int sc = rachelDropScore(tx, ty, p, seasonEpisode);
            if (sc < bestDropSc) { bestDropSc = sc; bestDropIdx = i; }
        }
    }

    int will_drop = 0;
    if (bestDropIdx != -1) {
        PackageInfo *dp = &packagesFanMail[bestDropIdx];
        if (tx == dp->dropoff_x && ty == dp->dropoff_y) {
            centralPerkBoard->dropOffCommands[t] = dp->id;
            dp->status = 2;
            dp->truck_id = -1;
            will_drop = 1;
        }
    }

    // best pick on current tile if capacity allows 
    int bestPickIdx = -1;
    int bestPickSc = INT_MAX;
    int curr_carry_for_pick = carry - will_drop;
    if (curr_carry_for_pick < AUTH_PKG_LIMIT) {
        for (int i = 0; i < fanMailCount; ++i) {
            PackageInfo *p = &packagesFanMail[i];
            if (p->status == 0 && tx == p->pickup_x && ty == p->pickup_y) {
                int sc = rachelPickupUrgency(seasonEpisode, p->expiry_turn);
                if (sc < bestPickSc) { bestPickSc = sc; bestPickIdx = i; }
            }
        }
    }

    int will_pick = 0;
    if (bestPickIdx != -1) {
        PackageInfo *pp = &packagesFanMail[bestPickIdx];
        centralPerkBoard->pickUpCommands[t] = pp->id;
        pp->status = 1;
        pp->truck_id = t;
        will_pick = 1;
    }

    int effective_carry = carry - will_drop + will_pick;

    // choose movement target 
    int targetX = -1, targetY = -1;
    if (effective_carry > 0) {
        int bestMoveSc = INT_MAX;
        for (int j = 0; j < fanMailCount; ++j) {
            PackageInfo *p = &packagesFanMail[j];
            if (p->status == 1 && p->truck_id == t) {
                int sc = rachelDropScore(tx, ty, p, seasonEpisode);
                if (sc < bestMoveSc) { bestMoveSc = sc; targetX = p->dropoff_x; targetY = p->dropoff_y; }
            }
        }
    } else {
        int bestMoveSc = INT_MAX;
        for (int j = 0; j < fanMailCount; ++j) {
            PackageInfo *p = &packagesFanMail[j];
            if (p->status == 0) {
                int dist = joeyCountBlocksLikePizzaSlices(tx, ty, p->pickup_x, p->pickup_y);
                int urg = rachelPickupUrgency(seasonEpisode, p->expiry_turn);
                int sc = 3 * dist + urg;
                if (sc < bestMoveSc) { bestMoveSc = sc; targetX = p->pickup_x; targetY = p->pickup_y; }
            }
        }
    }

    if (targetX == -1) { targetX = tx; targetY = ty; }

    // prefer staying if more local picks exist and capacity allows 
    if (effective_carry < AUTH_PKG_LIMIT) {
        for (int k = 0; k < fanMailCount; ++k) {
            PackageInfo *p = &packagesFanMail[k];
            if (p->status == 0 && tx == p->pickup_x && ty == p->pickup_y) { targetX = tx; targetY = ty; break; }
        }
    }

    char step = phoebeHumsAStep(tx, ty, targetX, targetY);
    centralPerkBoard->truckMovementInstructions[t] = step;

    // if moving while carrying cargo, produce auth string (clamped) 
    if (step != 's' && carry > 0) {
        int need = carry > AUTH_PKG_LIMIT ? AUTH_PKG_LIMIT : carry;
        rachelGuessTheSecretWord(t, need, centralPerkBoard->authStrings[t]);
    }
}
//Turn orchestartion 
static void rossProcessOneTurnVerySeriously(const TurnChangeResponse *note) {
    seasonEpisode = note->turnNumber;
    rossIngestNewPackages(note);
    rossClearTruckCommands();
    for (int t = 0; t < totalDepots; ++t) rossPickDropMoveForTruck(t);
}
//Main loop
int main(void) {
    chandlerReadStageDirections();
    monicaPrepTheCentralPerkIPC();

    while (1) {
        TurnChangeResponse noteFromProducer;
        if (msgrcv(centralBellQueue,
                   &noteFromProducer,
                   sizeof(noteFromProducer) - sizeof(long),
                   2, 0) == -1) {
            /* if receive fails, exit; keep behaviour same as original */
            break;
        }
        if (noteFromProducer.finished || noteFromProducer.errorOccurred) break;

        rossProcessOneTurnVerySeriously(&noteFromProducer);

        TurnReadyRequest curtainCall;
        curtainCall.mtype = 1;
        if (msgsnd(centralBellQueue,
                   &curtainCall,
                   sizeof(curtainCall) - sizeof(long),
                   0) == -1) {
            break;
        }
    }

    if (centralPerkBoard) (void)shmdt(centralPerkBoard);
    return 0;
}

