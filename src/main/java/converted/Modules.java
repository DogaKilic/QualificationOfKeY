package converted;

public final class Modules {

    final CycleResult cycleResult = new CycleResult();
    final TTCCalculation_state ttc_state = new TTCCalculation_state();
    final StoppingTimeCalculation_state stc_state = new StoppingTimeCalculation_state();
    final AEBLogic_state aeb_state = new AEBLogic_state();

    final int AEB_PB1_decel = 2, AEB_PB2_decel = 4, AEB_FB_decel = 8;

    final int THRESHOLD_VELOCITY_STOP = 3;

    /*@ public invariant
      @ AEB_PB1_decel == 2 && AEB_PB2_decel == 4 && AEB_FB_decel == 8 && THRESHOLD_VELOCITY_STOP == 3 && ttc_state.\inv && stc_state.\inv && aeb_state.\inv;
      @*/


    /*@ public normal_behaviour
      @ requires this.\inv &&  2 >= egoVelocity / AEB_PB1_decel && egoVelocity >= 0;
      @ assignable cycleResult.*, ttc_state.*, stc_state.*, aeb_state.*;
      @ ensures mioDistance >=4 ==> cycleResult.collision == false;
      @ ensures mioDistance <= 3 ==> cycleResult.collision == true;
      @ ensures mioVelocity >= 0 && egoVelocity >= THRESHOLD_VELOCITY_STOP ==> cycleResult.aebStatus == \old(cycleResult).aebStatus &&
                    cycleResult.fcwActivate == \old(cycleResult).fcwActivate && cycleResult.decelaration == \old(cycleResult).decelaration;
      @ ensures mioVelocity < 0 && egoVelocity >= THRESHOLD_VELOCITY_STOP ==> cycleResult.aebStatus >= \old(cycleResult).aebStatus;
      @ ensures this.\inv;
      @*/
    void cycle (int mioDistance, int mioVelocity, int egoVelocity) {
        cycleResult.mioDistance = mioDistance;
        cycleResult.mioVelocity = mioVelocity;
        cycleResult.egoVelocity = egoVelocity;

        ttc_state.mioDistance = mioDistance;
        ttc_state.mioVelocity = mioVelocity;
        ttc_state.ttcCalculation();
        cycleResult.collision = ttc_state.collision;

        stc_state.egoVelocity = egoVelocity;
        stc_state.FB1decel = AEB_PB1_decel;
        stc_state.FB2decel = AEB_PB2_decel;
        stc_state.FBdecel = AEB_FB_decel;
        stc_state.stoppingTimeCalculation();

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
        aeb_state.aebLogic();

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
    public void main() {
        int dist;
        int velo1;
        int velo2;
        /*@ loop_invariant
          @ true;
          @ assignable random.previous, cycleResult.mioDistance, cycleResult.mioVelocity, cycleResult.egoVelocity, ttc_state.mioDistance, ttc_state.mioVelocity, cycleResult.collision
                        , stc_state.egoVelocity, stc_state.FB1decel, stc_state.FB2decel, stc_state.FBdecel, ttc_state.collision, ttc_state.ttc
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
