package converted;

public final class AEBLogic_state {
    //Inputs
    int ttc, fcwTime, pb1Time, pb2Time, fbTime, fbDecel, pb1Decel, pb2Decel;
    boolean stop;
    //Outputs
    int fcwActivate, decel, aebStatus;
    //State
    int mode;

    final int M_DEFAULT = 0;
    final int M_FCW = 1;
    final int M_PARTIAL_BREAKING_1 = 2;
    final int M_PARTIAL_BREAKING_2 = 3;
    final int M_FULL_BREAKING = 4;

    /*@ public invariant
      @ M_DEFAULT == 0 && M_FCW == 1 && M_PARTIAL_BREAKING_1 == 2 && M_PARTIAL_BREAKING_2 == 3 && M_FULL_BREAKING == 4 &&
      @     (this.mode == M_DEFAULT || this.mode == M_FCW || this.mode == M_PARTIAL_BREAKING_1 || this.mode == M_PARTIAL_BREAKING_2
      @     || this.mode == M_FULL_BREAKING) && this != null && fcwTime >= pb1Time >= pb2Time >= fbTime >= 0 && fbDecel >= pb2Decel >= pb1Decel >= 0 && fcwActivate >= 0
            && decel >= 0 && aebStatus >= 0;
      @*/

    /*@ public normal_behaviour
      @ ensures mode == this.M_DEFAULT;
      @*/
    public AEBLogic_state() {
        this.mode = this.M_DEFAULT;
    }



    /*@ public normal_behaviour
      @ requires true;
      @ ensures x < 0 ==> \result == -x;
      @ ensures x >= 0 ==> \result == x;
      @ ensures this.\inv;
      @ assignable \nothing;
      @*/
    private int /*@ strictly_pure @*/ abs(int x) {
        return (x < 0) ? -x : x;
    }

    /*@ public normal_behavior
      @ requires this.\inv && fbDecel > pb2Decel > pb1Decel;
      @ assignable this.mode, this.aebStatus, this.fcwActivate, this.decel;
      @ ensures \old(mode) == 4 && stop ==> mode == 0;
      @ ensures ttc >= 0 && !stop ==> mode == \old(mode);
      @ ensures ttc >= 0 && stop ==> (mode == 0 || mode == 1);
      @ ensures ttc < 0 && !(abs(ttc) < (10*fcwTime) / 12) && !stop ==> mode >= \old(mode);
      @ ensures ttc < 0 && abs(ttc) < fbTime && mode < 4 && !stop ==> mode >= \old(mode);
      @ ensures this.\inv;
      @*/
    void aebLogic() {
        switch (this.mode){
            case M_DEFAULT:
                this.aebStatus = 0;
                this.fcwActivate = 0;
                this.decel = 0;

                if (abs(this.ttc) < this.fcwTime && this.ttc < 0) {
                    this.mode = M_FCW;
                }

                break;
            case M_FCW:
                this.aebStatus = 0;
                this.fcwActivate = 1;
                this.decel = 0;

                if (abs(this.ttc) < this.pb1Time && this.ttc < 0) {
                    this.mode = M_PARTIAL_BREAKING_1;
                } else if (abs(this.ttc) < (10 * this.fcwTime) / 12 && this.ttc < 0) {
                    this.mode = M_DEFAULT;
                }
                break;
            case M_PARTIAL_BREAKING_1:
                this.aebStatus = 1;
                this.fcwActivate = 1;
                this.decel = this.pb1Decel;

                if (abs(this.ttc) < this.pb2Time && this.ttc < 0) {
                    this.mode = M_PARTIAL_BREAKING_2;
                }
                else if (this.stop) {
                    this.mode = M_DEFAULT;
                }
                break;
            case M_PARTIAL_BREAKING_2:
                this.aebStatus = 2;
                this.fcwActivate = 1;
                this.decel = this.pb2Decel;

                if (abs(this.ttc) < this.fbTime && this.ttc < 0) {
                    this.mode = M_FULL_BREAKING;
                }
                else if (this.stop) {
                    this.mode = M_DEFAULT;
                }
                break;
            case M_FULL_BREAKING:
                this.aebStatus = 3;
                this.fcwActivate = 1;
                this.decel = this.fbDecel;

                if (this.stop) {
                    this.mode = M_DEFAULT;
                }
                break;
            default:
                assert false;
        }
    }
}
