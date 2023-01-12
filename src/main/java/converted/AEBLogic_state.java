package converted;

public final class AEBLogic_state {
    //Inputs
    int ttc, fcwTime, pb1Time, pb2Time, fbTime, fbDecel, pb1Decel, pb2Decel;
    boolean stop;
    //Outputs
    int fcwActivate, decel, aebStatus;
    //State
    int mode;

    private final int M_DEFAULT = 0;
    private final int M_FCW = 1;
    private final int M_PARTIAL_BREAKING_1 = 2;
    private final int M_PARTIAL_BREAKING_2 = 3;
    private final int M_FULL_BREAKING = 4;

    /*@ public invariant
      @ M_DEFAULT == 0 && M_FCW == 1 && M_PARTIAL_BREAKING_1 == 2 && M_PARTIAL_BREAKING_2 == 3 && M_FULL_BREAKING == 4 &&
      @     (this.mode == M_DEFAULT || this.mode == M_FCW || this.mode == M_PARTIAL_BREAKING_1 || this.mode == M_PARTIAL_BREAKING_2
      @     || this.mode == M_FULL_BREAKING);
      @*/

    /*@
      @ ensures mode == this.M_DEFAULT;
      @*/
    public AEBLogic_state() {
        this.mode = this.M_DEFAULT;
    }



    /*@ public normal_behaviour
      @ requires true;
      @ ensures x < 0 ==> \result == - x;
      @ ensures x >= 0 ==> \result == x;
      @ assignable \nothing;
      @*/
    private int /*@ strictly_pure helper @*/ abs(int x) {
        return (x < 0) ? -x : x;
    }

    /*@ public normal_behavior
      @ requires true;
      @ assignable this.mode, this.aebStatus, this.fcwActivate, this.decel;
      @ ensures \old(this.mode) == M_DEFAULT ==> this.decel == 0 && this.aebStatus == 0 && this.fcwActivate == 0;
      @ ensures \old(this.mode) == M_DEFAULT && abs(this.ttc) < this.fcwTime && this.ttc < 0 ==> this.mode == M_FCW;
      @ ensures \old(this.mode) == M_DEFAULT && !(abs(this.ttc) < this.fcwTime && this.ttc < 0) ==> this.mode == M_DEFAULT;
      @ ensures \old(this.mode) == M_FCW ==> this.decel == 0 && this.aebStatus == 0 && this.fcwActivate == 1;
      @ ensures \old(this.mode) == M_FCW && abs(this.ttc) < this.pb1Time && this.ttc < 0 ==> this.mode == M_PARTIAL_BREAKING_1;
      @ ensures \old(this.mode) == M_FCW && abs(this.ttc) >= this.pb1Time && abs(this.ttc) < (10 * this.fcwTime) / 12 && this.ttc < 0 ==> this.mode == M_DEFAULT;
      @ ensures \old(this.mode) == M_FCW && !(abs(this.ttc) < this.pb1Time && this.ttc < 0) && !(abs(this.ttc) >= this.pb1Time && abs(this.ttc) < (10 * this.fcwTime) / 12 && this.ttc < 0) ==> this.mode == M_FCW;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_1 ==> this.decel == this.pb1Decel && this.aebStatus == 1 && this.fcwActivate == 1;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_1 && abs(this.ttc) < this.pb2Time && this.ttc < 0 ==> this.mode == M_PARTIAL_BREAKING_2;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_1 && (abs(this.ttc) >= this.pb2Time || this.ttc >= 0) && this.stop ==> this.mode == M_DEFAULT;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_1 && !(abs(this.ttc) < this.pb2Time && this.ttc < 0) && !((abs(this.ttc) >= this.pb2Time || this.ttc >= 0) && this.stop) ==> this.mode == M_PARTIAL_BREAKING_1;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_2 ==> this.decel == this.pb2Decel && this.aebStatus == 2 && this.fcwActivate == 1;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_2 && abs(this.ttc) < this.fbTime && this.ttc < 0 ==> this.mode == M_FULL_BREAKING;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_2 && (abs(this.ttc) >= this.fbTime || this.ttc >= 0) && this.stop ==> this.mode == M_DEFAULT;
      @ ensures \old(this.mode) == M_PARTIAL_BREAKING_2 && !(abs(this.ttc) < this.fbTime && this.ttc < 0) && !((abs(this.ttc) >= this.fbTime || this.ttc >= 0) && this.stop) ==> this.mode == M_PARTIAL_BREAKING_2;
      @ ensures \old(this.mode) == M_FULL_BREAKING ==> this.decel == this.fbDecel && this.aebStatus == 3 && this.fcwActivate == 1;
      @ ensures \old(this.mode) == M_FULL_BREAKING && this.stop ==> this.mode == M_DEFAULT;
      @ ensures \old(this.mode) == M_FULL_BREAKING && !(this.stop) ==> this.mode == M_FULL_BREAKING;
      @ ensures (this.mode == this.M_DEFAULT || this.mode == this.M_FCW || this.mode == this.M_PARTIAL_BREAKING_1 || this.mode == this.M_PARTIAL_BREAKING_2 || this.mode == this.M_FULL_BREAKING);
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

                if (abs(this.ttc) < this.fbTime && this.ttc <0) {
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
