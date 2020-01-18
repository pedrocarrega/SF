/*
* @author Pedro Carrega, nº49480
*
* This program implements a printing system that receives requests from seperate clients
* Each printer can only handle one request at a time signalling
*/

#define printers 2 //number of printers
#define clients 3 //number of clients
#define buffer 5 //size of the printing buffer

chan print = [buffer] of {int, int, int, bool}; //asynchronous channel where printing requests are posted
chan answer = [printers] of {int, int}; //asynchronous channel where the printers notify clients

/*
* To check each property you must run the following commands in the command line:
*
* 1 - spin -a Print.pml
* 2 - gcc -o pan pan.c
* 3 - ./pan -a -f
* 4 - spin -t -p -g Print.pml (in case a property does not hold)
*/
ltl absense_of_starvation {eventually Printer@actived}
ltl will_finish {eventually Printer@finish && Client@collect}
//ltl busy {always Printer.notIdle && (Printer@goPrint || Printer@finish)}

/*
* Implementation of a printer
*/ 
active [printers] proctype Printer(){
    
    int id = _pid;
    int cId;
    int printed;
    int nPages;
    bool notIdle = false; //ghost variable
    int toPrint;

    goto actived;


    //printer is waiting for a request
    actived:

        notIdle = false; //ghost variable
        do
        :: print ?? [_, _, _, true] -> print ?? cId, nPages, toPrint, notIdle; //printer is now serving a client and wont take another request till it finishes
         //now would print first page
            printed++;
            goto goPrint
        od
    
    //printer received a request and now it's receiving the pages and printing them
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

/*
* Implementation of a client
*/
active [clients] proctype Client(){

    int id = _pid;
    int nPages = (id+1)*2;
    int pagesLeft = nPages;

    int printer;

    goto prints;

    
    //client will create and send a print request
    prints:

        //pagesLeft = nPages; //in case you want to print again
        
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

    
    //will now await an answer from the printer from where to collect his document
    collect:
        answer ?? [id, _] -> answer ?? _, printer;
        printf("Collect from printer %d\n", printer);
        goto stop; //change to prints in case you want to print again

    
    stop:
        skip;

}