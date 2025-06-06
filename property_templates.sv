`define MITER_DUV name_of_module_defining_miter

module property_checker(
	input reset,
	input clock

);

// library support for using Siemens EDA's OneSpin property checker
`include "tidal.sv" 

// The verification engineer has to create and define the used macro functions
// in the following included file:
`include "macros.sv"

`begin_tda(ops)

property SSC_DETECTION_UNROLLED;
	t ## 0 first_victim_mem_access() and		// This macro should constrain victim execution;
												// if core is blackboxed, it requires restriction
												// to the security-critical accesses
	t ## 0 instances_equivalent_except_core()	// miter setup: state variables from both instances
												// are equal except core, since its in control of the
												// attacker task
implies
	t ## 1 t1_cc_fanout() and					// fanout state variables reachable in n clock cycles
												// from data bus port of the core; function specifies
												// the respective state variables are equal b/w instances
	t ## 2 t2_cc_fanout() and
	t ## 3 t3_cc_fanout();
	// ...										// the idea is here to expand the proof to desired number
												// of unrollings
endproperty

unrolled_assertion: assert property ( @(posedge clock) disable iff(reset) SSC_DETECTION_UNROLLED);


property SSC_DETECTION_INDUCTIVE;
	t ## 0 victim_execution() and				// This macro should be used to avoid direct leackage
												// of secret data to persistent registers, i.e., in
												// a direct access. This also impacts possible invariants
	t ## 0 instances_equal_iteration_n()		// state variables from both instances are equal except
												// the once affected by secret data from the core. This
												// is an iterative procedure; it is useful to keep macros
												// from previous iterations for invariant formulation
												// Note that invariants are not featured here but may
												// become necessary to exclude false counterexamples
implies
	t ## 1 instances_equal_iteration_n();		// same macro in the property commitment for iteration n
endproperty

inductive_assertion: assert property ( @(posedge clock) disable iff(reset) SSC_DETECTION_INDUCTIVE);


`end_tda

endmodule

bind `MITER_DUV property_checker checker_bind(
	.reset(reset),
	.clock(clock));
