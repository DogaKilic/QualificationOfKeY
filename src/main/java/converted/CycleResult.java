package converted;

public final class CycleResult {

    /*@ public invariant
      @ this != null;
      @*/
    //INPUTS
    int mioDistance, mioVelocity, egoVelocity;
    boolean collision, egoCarStop;
    int fcwActivate, aebStatus, decelaration;
}
