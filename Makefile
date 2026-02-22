# ============================================================================
# Makefile wrapper for CMake build
# ============================================================================

BUILD_DIR := build

.PHONY: all run test clean

all:
	@mkdir -p $(BUILD_DIR)
	@cd $(BUILD_DIR) && cmake .. -DCMAKE_BUILD_TYPE=Release 2>&1 | tail -1
	@cmake --build $(BUILD_DIR) -- -j$$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
	@cp $(BUILD_DIR)/tctl_sat ./

run: all
ifndef FILE
	$(error Usage: make run FILE=<input.txt>)
endif
	@./$(BUILD_DIR)/tctl_sat $(FILE)

test: all
	@./$(BUILD_DIR)/tctl_sat --selftest

clean:
	@rm -rf $(BUILD_DIR)
