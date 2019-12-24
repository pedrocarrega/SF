import java.util.List;
import java.util.ArrayList;

public class Set{

private final List<Object> set;

    public Set() {
        //@ requires true;
        //@ ensures set.isEmpty();
        set = new ArrayList<Object>();
    }

    public boolean isEmpty() {
        //@ requires ;
        //@ ensures ;
        return set.isEmpty();
    }

    public int size() {
        //@ requires ;
        //@ ensures ;
        return set.size();
    }

    public void clear() {
        //@ requires ;
        //@ ensures ;
        set.removeAll(set);
    }

    public boolean contains(final Object o) {
        //@ requires ;
        //@ ensures ;
        return set.contains(o);
    }

    public void add(final Object o) {
        //@ requires ;
        //@ ensures ;
        set.add(o);
    }

    public void remove(final Object o) {
        //@ requires !set.isEmpty();
        //@ ensures ;
        set.remove(o);
    }




}