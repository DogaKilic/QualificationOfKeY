package converted;

public final class StoppingTimeCalculation_state {
    private int reactTime = 2;

    //Inputs
    int egoVelocity, FB1decel, FB2decel, FBdecel;
    //Outputs
    int FCWStoppingTime, PB1StoppingTime, PB2StoppingTime, FBStoppingTime;

    /*@ public invariant
      @ reactTime == 2 && FBdecel > 0 && FB1decel > 0 && FB2decel > 0 && FB1decel < FB2decel < FBdecel && this != null;
      @*/

    /*@ normal_behavior
      @ requires this.\inv;
      @ assignable this.FBStoppingTime, this.PB1StoppingTime, this.PB2StoppingTime, this.FCWStoppingTime;
      @ ensures this.egoVelocity >= 0 ==> this.PB1StoppingTime >= this.PB2StoppingTime >= this.FBStoppingTime;
      @ ensures this.egoVelocity < 0 ==> this.PB1StoppingTime <= this.PB2StoppingTime <= this.FBStoppingTime;
      @ ensures this.\inv;
      @*/
    void stoppingTimeCalculation() {
        this.FBStoppingTime = this.egoVelocity / this.FBdecel;
        this.PB2StoppingTime = this.egoVelocity / this.FB2decel;
        this.PB1StoppingTime = this.egoVelocity / this.FB1decel;
        this.FCWStoppingTime = this.FBStoppingTime + reactTime;
    }
}
