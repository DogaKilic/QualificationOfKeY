package converted;

public class RandomGen {

    final long a = 25214903917L;   // These Values for a and c are the actual values found
    final long c = 11;            // in the implementation of java.util.Random()
    long previous;

    /*@
      @ ensures previous == 32719;
      @*/
    public RandomGen() {
        previous = 32719;
    }

    /*@ public invariant
      @ a != null && c != null && previous != null && a == 25214903917L && c == 11 && previous >= 0;
      @*/

    /*@ public normal_behaviour
      @ requires true;
      @ assignable previous;
      @ ensures \result != null;
      @ ensures (int)((a * \old(previous) + c) % 32749) != 0 ==> \result == (int)((a * \old(previous) + c) % 32749);
      @ ensures (int)((a * \old(previous) + c) % 32749) == 0 ==> \result == 1;
      @ ensures \result != 0;
      @ ensures previous >= 0;
      @ ensures this.\inv;
      @*/
    int rand() {
        long r = (a * previous + c) % 32749;
        previous = r;
        if (r == 0) {
            return 1;
        }
        return (int)r;
    }

}
