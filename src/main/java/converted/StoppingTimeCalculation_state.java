package converted;

public final class StoppingTimeCalculation_state {
    private int reactTime = 2;

    //Inputs
    int egoVelocity, FB1decel, FB2decel, FBdecel;
    //Outputs
    int FCWStoppingTime, PB1StoppingTime, PB2StoppingTime, FBStoppingTime;

    /*@ public invariant
      @ reactTime == 2 && FBdecel > 0 && FB1decel > 0 && FB2decel > 0 && FB2decel < FB1decel < FBdecel;
      @*/

    /*@ normal_behavior
      @ requires true;
      @ assignable this.FBStoppingTime, this.PB1StoppingTime, this.PB2StoppingTime, this.FCWStoppingTime;
      @ //ensures this.egoVelocity >= 0 ==> this.PB2StoppingTime >= this.PB1StoppingTime >= this.FBStoppingTime;
      @ //ensures this.egoVelocity < 0 ==> this.PB2StoppingTime <= this.PB1StoppingTime <= this.FBStoppingTime;
      @ ensures this.FBStoppingTime == this.egoVelocity / this.FBdecel;
      @ ensures this.PB1StoppingTime == this.egoVelocity / this.FB1decel;
      @ ensures this.PB2StoppingTime == this.egoVelocity / this.FB2decel;
      @ ensures this.FCWStoppingTime == this.FBStoppingTime + reactTime;
      @ ensures this.\inv;
      @*/
    void stoppingTimeCalculation() {
        this.FBStoppingTime = this.egoVelocity / this.FBdecel;
        this.PB1StoppingTime = this.egoVelocity / this.FB1decel;
        this.PB2StoppingTime = this.egoVelocity / this.FB2decel;
        this.FCWStoppingTime = this.FBStoppingTime + reactTime;
    }
}
