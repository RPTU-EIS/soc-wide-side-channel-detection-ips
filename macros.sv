// Macro functions for side-channel detection properties
// These automatic functions are used in the property templates for
// SoC-wide side-channel detection verification

`define MITER_INST_1 name_of_first_duv_instance
`define MITER_INST_2 name_of_second_duv_instance


// Function to constrain victim execution
// Should restrict to security-critical accesses if core is blackboxed
function automatic first_victim_mem_access();
    // TODO: Implement logic to identify first victim memory access
    // This should constrain the victim execution to security-critical operations
    first_victim_mem_access = 1'b1; // Placeholder - replace with actual implementation
endfunction

// Miter setup function - checks if state variables from both instances
// are equal except for the core (which is under attacker control)
function automatic instances_equivalent_except_core();
    // TODO: Implement logic to compare all state variables except core state
    // This function should return true when both miter instances have identical
    // state except for the core registers/signals
    instances_equivalent_except_core = 1'b1; // Placeholder - replace with actual implementation
endfunction

// Fanout state variables reachable in 1 clock cycle from core data bus
function automatic t1_cc_fanout();
    // TODO: Implement logic to check if fanout state variables are equal
    // between instances after 1 clock cycle from core data bus access
    // This captures immediate propagation effects
    t1_cc_fanout = 1'b1; // Placeholder - replace with actual implementation
endfunction

// Fanout state variables reachable in 2 clock cycles from core data bus
function automatic t2_cc_fanout();
    // TODO: Implement logic to check if fanout state variables are equal
    // between instances after 2 clock cycles from core data bus access
    // This captures secondary propagation effects
    t2_cc_fanout = 1'b1; // Placeholder - replace with actual implementation
endfunction

// Fanout state variables reachable in 3 clock cycles from core data bus
function automatic t3_cc_fanout();
    // TODO: Implement logic to check if fanout state variables are equal
    // between instances after 3 clock cycles from core data bus access
    // This captures tertiary propagation effects
    t3_cc_fanout = 1'b1; // Placeholder - replace with actual implementation
endfunction

// Function to identify victim execution while avoiding direct leakage
// Should prevent direct leakage of secret data to persistent registers
function automatic victim_execution();
    // TODO: Implement logic to identify victim execution phases
    // This should exclude direct access patterns that would cause obvious leakage
    // Focus on indirect side-channel effects rather than direct data exposure
    victim_execution = 1'b1; // Placeholder - replace with actual implementation
endfunction

// Iterative equality check for state variables between instances
// Used in inductive approach - excludes variables affected by secret data
function automatic instances_equal_iteration_n();
    // TODO: Implement iterative equality check for state variables
    // This is part of an iterative refinement process where variables
    // affected by secret data are progressively identified and excluded
    // Keep macros from previous iterations for invariant formulation
    instances_equal_iteration_n = 1'b1; // Placeholder - replace with actual implementation
endfunction

