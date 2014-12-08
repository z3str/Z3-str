#include "strTheory.h"

std::string inputFile;

int main(int argc, char ** argv)
{
    logFile = NULL;
    std::string primStr;
    inputFile = std::string("");
    int c;

#ifdef DEBUGLOG
    logFile = fopen("log", "w");
#endif

    static struct option long_options[] =
    {
        { "input", required_argument, 0, 'f' },
        { "help", no_argument, 0, 'h' },
        { "allowloopcut", no_argument, 0, 'p' },
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;
        c = getopt_long(argc, argv, "hpf:l:", long_options, &option_index);

        if (c == -1)
            break;

        switch (c)
        {
            case 'f':
            {
                inputFile = std::string(optarg);
                break;
            }
            case 'p':
            {
                // Allow loop cut
                // May not terminate on some input
                avoidLoopCut = false;
                break;
            }
            case 'h':
            {
                break;
            }
            default:
                exit(0);
        }
    }
#ifdef DEBUGLOG
    printf("Input File: %s\n\n", inputFile.c_str());
    __debugPrint(logFile, "Input file: %s\n\n", inputFile.c_str());
#endif

    pa_theory_example();

#ifdef DEBUGLOG
    fclose(logFile);
#endif

    return 0;
}

