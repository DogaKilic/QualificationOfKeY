package converted;

public final class TTCCalculation_state {

    //Inputs
    int mioDistance;
    int mioVelocity;
    //Outputs
    boolean collision;
    int ttc;

    private int headwayOffset = 3;

    /*@ public invariant
      @ headwayOffset == 3;
      @*/

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
      @ ensures (\result >= l && \result <= u) || (\result <= l && \result >= u);
      @ assignable \nothing;
      @*/
    int clamp(int l, int x, int u) { return min(max(x, l), u); }

    /*@ public normal_behavior
      @ requires this.\inv;
      @ assignable this.collision, this.ttc;
      @ ensures this.mioVelocity < 0 ==> this.ttc == -((this.mioDistance - this.headwayOffset) / clamp(10, -this.mioVelocity, 150));
      @ ensures this.mioVelocity >= 0 ==> this.ttc == (this.mioDistance - this.headwayOffset) / clamp(10, this.mioVelocity, 150);
      @ ensures 10 * (this.mioDistance - this.headwayOffset) < 1 ==> this.collision == true;
      @ ensures 10 * (this.mioDistance - this.headwayOffsetmi) >= 1 ==> this.collision == false;
      @ ensures this.\inv;
      @*/
    void ttcCalculation() {
        int headway = this.mioDistance - headwayOffset;
        int abs = this.mioVelocity < 0 ? -(this.mioVelocity) : this.mioVelocity;
        int signum = this.mioVelocity < 0 ? -1 : 1;
        int clamped = clamp(10, abs, 150);
        int ttc = headway / clamped;

        this.ttc = ttc * signum;

        this.collision = (10 * headway < 1);
    }

}
