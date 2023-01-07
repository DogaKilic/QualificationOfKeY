package converted;

public class Modules {
    //globals
    int headawayOffset = 3;
    int reactTime = 2;

    /*@   public invariant
      @    headawayOffset > 0 && reactTime > 0;
      @*/

    /*@ public normal_behaviour
      @ requires true;
      @ ensures x < 0 ==> \result == - \old(x);
      @ ensures x >= 0 ==> \result == \old(x);
      @ assignable x;
      @*/
    int abs(int x) { return x < 0 ? -x : x;}
    /*@ public normal_behaviour
      @ requires true;
      @ ensures x < y ==> \result == x;
      @ ensures x >= y ==> \result == y;
      @ assignable \nothing;
      @*/
    int min(int x, int y) { return x < y ? x : y; }
    /*@ public normal_behaviour
      @ requires true;
      @ ensures x > y ==> \result == x;
      @ ensures y >= x ==> \result == y;
      @ assignable \nothing;
      @*/
    int max(int x, int y) { return x > y ? x : y; }
    /*@ public normal_behavior
      @ requires true;
      @ ensures x >= u || l >= u ==> \result == u;
      @ ensures l <= u && x <= u && l >= x ==> \result == l;
      @ ensures l <= u && x <= u && x >= l ==> \result == x;
      @ ensures l <= u && x <= u && l == x ==> \result == l && \result == x;
      @ ensures l <= u && x <= u && l == x && x == u ==> \result == l && \result == x && \result == u;
      @ assignable \nothing;
      @*/
    int clamp(int l, int x, int u) { return min(max(x, l), u); }

    /*@ public normal_behavior
      @ requires state != null && state.mioVelocity != 0;
      @ assignable state.colission, state.ttc;
      @ ensures (state.mioVelocity <= 25 ==> state.ttc == 0);
      @ ensures (state.mioVelocity > 25 ==> state.ttc == (128 * \old(state.mioDistance)) / clamp(10, \old(state.mioVelocity),150));
      @ ensures state.ttc != null;
      @ ensures (state.mioDistance) < 13 ==> state.colission == true;
      @ ensures (state.mioDistance) >= 13 ==> state.colission == false;
      @*/
     void ttcCalculation(TTCCalculation_state state) {
        int headaway = 0;
        headaway = state.mioDistance - headaway;
        int abs = state.mioVelocity < 0 ? -(state.mioVelocity) : state.mioVelocity;
        int clamped = clamp(10, abs, 150);
        int ttc = 128 * headaway / clamped;


        if (state.mioVelocity > 25) {
            state.ttc = ttc;
        }
        else {
            state.ttc = 0;
        }

        state.colission = (headaway < 13);
    }

    /*@ public normal_behavior
      @ requires state != null && state.FB1decel != 0 && state.FBdecel != 0 && state.FB2decel != 0;
      @ assignable state.FBStoppingTime, state.PB1StoppingTime, state.PB2StoppingTime, state.FCWStoppingTime;
      @ ensures state.FBStoppingTime == state.egoVelocity / state.FBdecel;
      @ ensures state.PB1StoppingTime == state.egoVelocity / state.FB1decel;
      @ ensures state.PB2StoppingTime == state.egoVelocity / state.FB2decel;
      @ ensures state.FCWStoppingTime == state.FBStoppingTime + reactTime;
      @*/
    void stoppingTimeCalculation(StoppingTimeCalculation_state state) {
        state.FBStoppingTime = state.egoVelocity / state.FBdecel;
        state.PB1StoppingTime = state.egoVelocity / state.FB1decel;
        state.PB2StoppingTime = state.egoVelocity / state.FB2decel; //???  PB1StoppingTime to PB2StoppingTime
        state.FCWStoppingTime = state.FBStoppingTime + reactTime;
    }

    final int M_DEFAULT = 0, M_FCW = 1, M_PARTIAL_BREAKING_1 = 2,
            M_PARTIAL_BREAKING_2 = 3, M_FULL_BREAKING = 4;

    /*@ public normal_behavior
      @ requires s != null && s.ttc != null && (s.mode == 0 || s.mode == 1 || s.mode == 2 || s.mode == 3 || s.mode == 4);
      @ assignable s.mode, s.aebStatus, s.fcwActivate, s.decel;
      @ ensures \old(s.mode) == 0 ==> s.decel == 0 && s.aebStatus == 0 && s.fcwActivate == 0;
      @ ensures \old(s.mode) == 0 && abs(s.ttc) < s.fcwTime && s.ttc < 0 ==> s.mode == M_FCW;
      @ ensures \old(s.mode) == 1 ==> s.decel == 0 && s.aebStatus == 0 && s.fcwActivate == 1;
      @ ensures \old(s.mode) == 1 && abs(s.ttc) < s.pb1Time && s.ttc < 0 ==> s.mode == M_PARTIAL_BREAKING_1;
      @ ensures \old(s.mode) == 1 && abs(s.ttc) >= s.pb1Time && abs(s.ttc) < (10 * s.fcwTime) / 12 && s.ttc < 0 ==> s.mode == M_DEFAULT;
      @ ensures \old(s.mode) == 2 ==> s.decel == s.pb1Decel && s.aebStatus == 1 && s.fcwActivate == 1;
      @ ensures \old(s.mode) == 2 && abs(s.ttc) < s.pb2Time && s.ttc < 0 ==> s.mode == M_PARTIAL_BREAKING_2;
      @ ensures \old(s.mode) == 2 && (abs(s.ttc) >= s.pb2Time || s.ttc >= 0) && s.stop ==> s.mode == M_DEFAULT;
      @ ensures \old(s.mode) == 3 ==> s.decel == s.pb2Decel && s.aebStatus == 2 && s.fcwActivate == 1;
      @ ensures \old(s.mode) == 3 && abs(s.ttc) < s.fbTime && s.ttc < 0 ==> s.mode == M_FULL_BREAKING;
      @ ensures \old(s.mode) == 3 && (abs(s.ttc) >= s.fbTime || s.ttc >= 0) && s.stop ==> s.mode == M_DEFAULT;
      @ ensures \old(s.mode) == 4 ==> s.decel == s.fbDecel && s.aebStatus == 3 && s.fcwActivate == 1;
      @ ensures \old(s.mode) == 4 && s.stop ==> s.mode == M_DEFAULT;
      @*/
    void aebLogic(AEBLogic_state s) {
        switch (s.mode){
            case 0://M_DEFAULT
                s.aebStatus = 0;
                s.fcwActivate = 0;
                s.decel = 0;

                if (abs(s.ttc) < s.fcwTime && s.ttc < 0) {
                    s.mode = M_FCW;
                }

                break;
            case 1://M_FCW
                s.aebStatus = 0;
                s.fcwActivate = 1;
                s.decel = 0;

                if (abs(s.ttc) < s.pb1Time && s.ttc < 0) {
                    s.mode = M_PARTIAL_BREAKING_1;
                } else if (abs(s.ttc) < (10 * s.fcwTime) / 12 && s.ttc < 0) {
                    s.mode = M_DEFAULT;
                }
                break;
            case 2://M_PARTIAL_BREAKING_1
                s.aebStatus = 1;
                s.fcwActivate = 1;
                s.decel = s.pb1Decel;

                if (abs(s.ttc) < s.pb2Time && s.ttc < 0) {
                    s.mode = M_PARTIAL_BREAKING_2;
                }
                else if (s.stop) {
                    s.mode = M_DEFAULT;
                }
                break;
            case 3://M_PARTIAL_BREAKING_2
                s.aebStatus = 2;
                s.fcwActivate = 1;
                s.decel = s.pb2Decel;

                if (abs(s.ttc) < s.fbTime && s.ttc <0) {
                    s.mode = M_FULL_BREAKING;
                }
                else if (s.stop) {
                    s.mode = M_DEFAULT;
                }
                break;
            case 4://M_FULL_BREAKING
                s.aebStatus = 3;
                s.fcwActivate = 1;
                s.decel = s.fbDecel;

                if (s.stop) {
                    s.mode = M_DEFAULT;
                }
                break;
            default:
                assert false;
        }
    }

    CycleResult cycleResult = new CycleResult();
    TTCCalculation_state ttc_state = new TTCCalculation_state();
    StoppingTimeCalculation_state stc_state = new StoppingTimeCalculation_state();
    AEBLogic_state aeb_state = new AEBLogic_state();

    final int AEB_PB1_decel = 2, AEB_PB2_decel = 4, AEB_FB_decel = 8;
    final int THRESHOLD_VELOCITY_STOP = 3;
    /*@ public normal_behaviour
      @ requires mioDistance != null && mioVelocity != null && egoVelocity != null && mioVelocity != 0 &&
                        AEB_PB1_decel != 0 && AEB_PB2_decel != 0 && AEB_FB_decel != 0 && ttc_state != null && stc_state != null && aeb_state != null && cycleResult != null &&
                        ttc_state.ttc != null && (aeb_state.mode == 0 || aeb_state.mode == 1 || aeb_state.mode == 2 || aeb_state.mode == 3 || aeb_state.mode == 4) && aeb_state.ttc != null;
      @ assignable cycleResult.mioDistance, cycleResult.mioVelocity, cycleResult.egoVelocity, ttc_state.mioDistance, ttc_state.mioVelocity, cycleResult.collision
                        , stc_state.egoVelocity, stc_state.FB1decel, stc_state.FB2decel, stc_state.FBdecel, ttc_state.colission, ttc_state.ttc
                        , stc_state.FCWStoppingTime, stc_state.PB1StoppingTime, stc_state.PB2StoppingTime, stc_state.FBStoppingTime
                        , aeb_state.ttc, aeb_state.fcwTime, aeb_state.pb1Time, aeb_state.pb2Time, aeb_state.fbTime, aeb_state.pb1Decel
                        , aeb_state.pb2Decel, aeb_state.fbDecel, cycleResult.egoCarStop, aeb_state.stop
                        , aeb_state.mode, aeb_state.aebStatus, aeb_state.fcwActivate, aeb_state.decel
                        , cycleResult.fcwActivate, cycleResult.aebStatus, cycleResult.decelaration;
      @ ensures cycleResult.mioDistance == mioDistance && cycleResult.mioVelocity == mioVelocity && cycleResult.egoVelocity == egoVelocity;
      @ ensures ttc_state.mioDistance == mioDistance && ttc_state.mioVelocity == mioVelocity;
      @ ensures cycleResult.collision == ttc_state.colission;
      @ ensures stc_state.egoVelocity == egoVelocity && stc_state.FB1decel == AEB_PB1_decel && stc_state.FB2decel == AEB_PB2_decel
                        && stc_state.FBdecel == AEB_FB_decel;
      @ ensures aeb_state.ttc == ttc_state.ttc && aeb_state.fcwTime == stc_state.FCWStoppingTime && aeb_state.pb1Time == stc_state.PB1StoppingTime
                        && aeb_state.pb2Time == stc_state.PB2StoppingTime && aeb_state.fbTime == stc_state.FBStoppingTime
                        && aeb_state.pb1Decel == AEB_PB1_decel && aeb_state.pb2Decel == AEB_PB2_decel && aeb_state.fbDecel == AEB_FB_decel;
      @ ensures cycleResult.egoCarStop == egoVelocity < THRESHOLD_VELOCITY_STOP;
      @ ensures aeb_state.stop == cycleResult.egoCarStop;
      @ ensures cycleResult.fcwActivate == aeb_state.fcwActivate && cycleResult.aebStatus == aeb_state.aebStatus && cycleResult.decelaration == aeb_state.decel;
      @*/
    void cycle (int mioDistance, int mioVelocity, int egoVelocity) {
        cycleResult.mioDistance = mioDistance;
        cycleResult.mioVelocity = mioVelocity;
        cycleResult.egoVelocity = egoVelocity;

        ttc_state.mioDistance = mioDistance;
        ttc_state.mioVelocity = mioVelocity;
        ttcCalculation(ttc_state);
        cycleResult.collision = ttc_state.colission;

        stc_state.egoVelocity = egoVelocity;
        stc_state.FB1decel = AEB_PB1_decel;
        stc_state.FB2decel = AEB_PB2_decel;
        stc_state.FBdecel = AEB_FB_decel;
        stoppingTimeCalculation(stc_state);

        aeb_state.ttc = ttc_state.ttc;
        aeb_state.fcwTime = stc_state.FCWStoppingTime;
        aeb_state.pb1Time = stc_state.PB1StoppingTime;
        aeb_state.pb2Time = stc_state.PB2StoppingTime;
        aeb_state.fbTime = stc_state.FBStoppingTime;
        aeb_state.pb1Decel = AEB_PB1_decel;
        aeb_state.pb2Decel = AEB_PB2_decel;
        aeb_state.fbDecel = AEB_FB_decel;

        cycleResult.egoCarStop = egoVelocity < THRESHOLD_VELOCITY_STOP;
        aeb_state.stop = cycleResult.egoCarStop;
        aebLogic(aeb_state);


        cycleResult.fcwActivate = aeb_state.fcwActivate;
        cycleResult.aebStatus = aeb_state.aebStatus;
        cycleResult.decelaration = aeb_state.decel;
    }

     RandomGen random = new RandomGen();

    /*@ public normal_behaviour
      @ requires random.\inv && random != null;
      @ assignable random.previous;
      @ ensures \result != null && \result != 0;
      @ ensures random.\inv;
      @*/
    public int nondet_int() {return random.rand();}

    /*@ public normal_behaviour
      @ requires random.\inv && random != null && this.nondet_int() != null && this.nondet_int() != 0 && AEB_PB1_decel != 0 && AEB_PB2_decel != 0 && AEB_FB_decel != 0 && ttc_state != null && stc_state != null && aeb_state != null && cycleResult != null &&
                        ttc_state.ttc != null && (aeb_state.mode == 0 || aeb_state.mode == 1 || aeb_state.mode == 2 || aeb_state.mode == 3 || aeb_state.mode == 4) && aeb_state.ttc != null;
      @ assignable random.previous, cycleResult.mioDistance, cycleResult.mioVelocity, cycleResult.egoVelocity, ttc_state.mioDistance, ttc_state.mioVelocity, cycleResult.collision
                        , stc_state.egoVelocity, stc_state.FB1decel, stc_state.FB2decel, stc_state.FBdecel, ttc_state.colission, ttc_state.ttc
                        , stc_state.FCWStoppingTime, stc_state.PB1StoppingTime, stc_state.PB2StoppingTime, stc_state.FBStoppingTime
                        , aeb_state.ttc, aeb_state.fcwTime, aeb_state.pb1Time, aeb_state.pb2Time, aeb_state.fbTime, aeb_state.pb1Decel
                        , aeb_state.pb2Decel, aeb_state.fbDecel, cycleResult.egoCarStop, aeb_state.stop
                        , aeb_state.mode, aeb_state.aebStatus, aeb_state.fcwActivate, aeb_state.decel
                        , cycleResult.fcwActivate, cycleResult.aebStatus, cycleResult.decelaration;
      @ ensures true;
      @ diverges true;
      @*/
    public void main() {
        int dist;
        int velo1;
        int velo2;
        /*@ loop_invariant
          @ true;
          @ assignable random.previous, cycleResult.mioDistance, cycleResult.mioVelocity, cycleResult.egoVelocity, ttc_state.mioDistance, ttc_state.mioVelocity, cycleResult.collision
                        , stc_state.egoVelocity, stc_state.FB1decel, stc_state.FB2decel, stc_state.FBdecel, ttc_state.colission, ttc_state.ttc
                        , stc_state.FCWStoppingTime, stc_state.PB1StoppingTime, stc_state.PB2StoppingTime, stc_state.FBStoppingTime
                        , aeb_state.ttc, aeb_state.fcwTime, aeb_state.pb1Time, aeb_state.pb2Time, aeb_state.fbTime, aeb_state.pb1Decel
                        , aeb_state.pb2Decel, aeb_state.fbDecel, cycleResult.egoCarStop, aeb_state.stop
                        , aeb_state.mode, aeb_state.aebStatus, aeb_state.fcwActivate, aeb_state.decel
                        , cycleResult.fcwActivate, cycleResult.aebStatus, cycleResult.decelaration;
          @*/
        while (true) {
            dist = nondet_int();
            velo1 = nondet_int();
            velo2 = nondet_int();
            cycle(dist, velo1, velo2);
        }
    }
}
