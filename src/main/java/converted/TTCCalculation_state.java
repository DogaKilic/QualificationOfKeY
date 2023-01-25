package converted;

public final class TTCCalculation_state {

    //Inputs
    int mioDistance;  //relative distance
    int mioVelocity;  // relative velocity
    //Outputs
    boolean collision; // have the vehicles collided
    int ttc; // not actually time to collapse abs(ttc) is actual time to collapse when ttc < 0 because it's calculated from relative velo and dist

    private final int headwayOffset = 3;

    /*@ public invariant
      @ headwayOffset == 3;
      @*/

    /*@ public normal_behaviour
      @ requires true;
      @ ensures x < y ==> \result == x;
      @ ensures x > y ==> \result == y;
      @ ensures x == y ==> \result == x && \result == y;
      @ assignable \nothing;
      @*/
    private int min(int x, int y) { return x < y ? x : y; }
    /*@ public normal_behaviour
      @ requires true;
      @ ensures x > y ==> \result == x;
      @ ensures y > x ==> \result == y;
      @ ensures y == x ==> \result == x && \result == y;
      @ assignable \nothing;
      @*/
    private int max(int x, int y) { return x > y ? x : y; }
    /*@ public normal_behavior
      @ requires l <= u;
      @ assignable \nothing;
      @ ensures x <= l ==> \result == l;
      @ ensures x >= u ==> \result == u;
      @ ensures l < x < u ==> \result == x;
      @ ensures this.\inv;
      @*/
    private int clamp(int l, int x, int u) { return min(max(x, l), u); }

    /*@ public normal_behavior
      @ requires this.\inv;
      @ assignable this.collision, this.ttc;
      @ ensures collision == 10 * (mioDistance - 3) < 1 ? true : false;
      @ ensures (mioVelocity >= 0) ==> (ttc >= 0);
      @ //ensures mioVelocity < 0 ==> ttc <= 0;
      @ ensures this.\inv;
      @*/
    void ttcCalculation() {
        int headway = this.mioDistance - headwayOffset <= 0 ? 0 : this.mioDistance - headwayOffset;
        int abs = this.mioVelocity < 0 ? -(this.mioVelocity) : this.mioVelocity;
        int signum = this.mioVelocity < 0 ? -1 : 1;
        int clamped = clamp(10, abs, 150); // 00.1 and 100 in matlab
        int ttc = headway / clamped;
        this.ttc = ttc * signum;

        this.collision = (10 * headway < 1);
    }

}
