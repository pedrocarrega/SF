#define printers 2 //number of printers
#define clients 3 //number of clients
#define buffer 10 //size of the printing buffer

chan print = [buffer] of {int, int, int, bool};
chan answer = [printers] of {int, int};

ltl absense_of_starvation {eventually Printer@actived}
ltl will_finish {eventually Printer@finish && Client@collect}

active [printers] proctype Printer(){
    
    int id = _pid;
    int cId;
    int printed;
    int nPages;
    bool notIdle = false; //ghost variable
    int toPrint;


    actived:

        notIdle = false;
        do
        :: print ?? [_, _, _, true] -> print ?? cId, nPages, toPrint, notIdle; //printer is now serving a client and wont take another request till it ends
         //now would print first page
            printed++;
            goto goPrint
        od
    
    goPrint:
        do
        :: if
            :: printed == nPages -> goto finish;
            :: else -> print ? [cId, nPages, _, false] -> print ? cId, _, toPrint, _; //now the printer would print
                printed++
        fi
        od

    //notify client that printing is complete
    finish:
        answer ! cId, id;
        printed = 0;
        goto actived;
}

active [clients] proctype Client(){

    int id = _pid;
    int nPages = (id+1)*2;
    int pagesLeft;

    int printer;

    prints:

        pagesLeft = nPages;
        
        do
        :: if
            :: pagesLeft == 0 -> goto collect;
            :: else -> if 
                        :: pagesLeft != nPages -> print ! id, nPages, id, false;
                            pagesLeft--
                        :: else -> print ! id, nPages, id, true
                        fi
            fi
        od

    
    collect:
        answer ?? [id, _] -> answer ?? _, printer;
        printf("Collect from printer %d\n", printer);
        goto stop;

    stop:
        skip;

}