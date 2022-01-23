#
# This is an example Makefile for a countwords program.  This
# program uses both the scanner module and a counter module.
# Typing 'make' or 'make count' will create the executable file.
#

# define some Makefile variables for the compiler and compiler flags
# to use Makefile variables later in the Makefile: $()
#
#  -g    adds debugging information to the executable file
#  -Wall turns on most, but not all, compiler warnings
#
# for C++ define  CC = g++
CC = g++
CFLAGS  = -g -std=c++11
# define any directories containing header files other than /usr/include
#
# INCLUDES = -I/home/newhall/include  -I../include

# define library paths in addition to /usr/lib
#   if I wanted to include libraries not in /usr/lib I'd specify
#   their path using -Lpath, something like:
LFLAGS = -L../build/lib

# define any libraries to link into executable:
#   if I want to link in libraries (libx.so or libx.a) I use the -llibname 
#   option, something like (this will link in libmylib.so and libm.so:
LIBS = -lclingo -lgringo -lpotassco -lclasp -lreify -lpthread

# typing 'make' will invoke the first target entry in the file 
# (in this case the default target entry)
# you can name this target entry anything, but "default" or "all"
# are the most commonly used names by convention
#
default: shared
MAIN = approxasp
SRCS = EGaussian.cpp packedrow.cpp test.cpp model_counting.cpp propagator.cpp utility.cpp
OBJDIR = Obj
OBJS = $(patsubst %.cpp,$(OBJDIR)/%.o,$(SRCS))

# To create the executable file count we need the object files
# countwords.o, counter.o, and scanner.o:
#
$(OBJDIR):
	mkdir -p $(OBJDIR)

shared: $(OBJDIR) $(OBJS) 
	$(CC) $(CFLAGS) -o $(MAIN) $(OBJS) -lclingo

static: $(OBJDIR) $(OBJS) 
	$(CC) $(CFLAGS) -static -o $(MAIN) $(OBJS) $(LFLAGS) $(LIBS)

# To create the object file countwords.o, we need the source
# files countwords.c, scanner.h, and counter.h:
#
$(OBJDIR)/%.o: %.cpp
	$(CC) $(CFLAGS) -c $<  -o $@
# To create the object file counter.o, we need the source files
# counter.c and counter.h:
#
# counter.o:  counter.c counter.h 
# 	$(CC) $(CFLAGS) -c counter.c

# To start over from scratch, type 'make clean'.  This
# removes the executable file, as well as old .o object
# files and *~ backup files:
#
clean:
	$(RM) *.o *~ $(MAIN) $(OBJDIR)/*
	$(RM) -rf $(OBJDIR)

