package converted;

public class AEBLogic_state {
    //Inputs
    int ttc, fcwTime, pb1Time, pb2Time, fbTime, fbDecel, pb1Decel, pb2Decel;
    boolean stop;
    //Outputs
    int fcwActivate, decel, aebStatus;
    //State
    int mode;

    /*@
      @ ensures mode == Modules.M_DEFAULT;
      @*/
    public AEBLogic_state() {
        this.mode = Modules.M_DEFAULT;
    }
}
