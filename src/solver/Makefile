SRC = summarizer_base.cpp \
      summarizer_bw.cpp	\
      summarizer_bw_term.cpp \
      summarizer_bw_cex.cpp \
      summarizer_bw_cex_ai.cpp \
      summarizer_bw_cex_complete.cpp \
      summarizer_bw_cex_concrete.cpp \
      summarizer_bw_cex_all.cpp \
      summarizer_bw_cex_wp.cpp \
      summarizer_fw_contexts.cpp \
      summarizer_fw.cpp \
      summarizer_fw_term.cpp \
      summary.cpp \
      summary_db.cpp \
      # empty last line

include ../config.inc
include $(CBMC)/src/config.inc
include $(CBMC)/src/common
CBMC ?= ../..

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CBMC)/src -I ..

CP_CXXFLAGS += $(SUMMARIZERFLAGS)

CLEANFILES = solver$(LIBEXT)

all: solver$(LIBEXT)

###############################################################################

solver$(LIBEXT): $(OBJ)
	$(LINKLIB)
