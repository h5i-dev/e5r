# Practical OSS PTX batch scoreboard

Target: approximately 50 distinct real OSS kernels. Practical totals: {'optimization_attempt': 12, 'gpu_tested': 12, 'fair_timing': 2, 'proof_attempt': 1, 'strict_accepted': 1, 'accepted_win': 0}.

Source/build screens do not count as optimization or proof attempts. A direct edit alone does not count as a completed attempt. Strict acceptance requires the exact bound programs, direct universal equivalence, safety/races/progress/frame, replay, axiom audit and negatives. Timing wins require normal and strongest applicable baseline evidence.

| Kernel | Phase | Edited | GPU | Fair timing | Proof attempted | Strict accepted |
| --- | --- | --- | --- | --- | --- | --- |
| catboost/make_sequence | source_build_screen | False | False | False | False | False |
| catboost/fill_buffer | source_build_screen | False | False | False | False | False |
| catboost/inverse_permutation | source_build_screen | False | False | False | False | False |
| catboost/reverse | edited_gpu_timed_proof_pending | True | True | False | False | False |
| catboost/gather_mask | source_build_screen | False | False | False | False | False |
| catboost/zero_segments | strict_direct_proof_accepted_normal_TU_pending | True | True | False | True | True |
| catboost/zero_partitions | edited_gpu_timed_proof_pending | True | True | False | False | False |
| catboost/update_partition_sizes | source_build_screen | False | False | False | False | False |
| catboost/fill_query_end_mask | edited_gpu_timed_proof_pending | True | True | False | False | False |
| catboost/compute_group_ids | edited_gpu_timed_proof_pending | True | True | False | False | False |
| catboost/compress | source_build_screen | False | False | False | False | False |
| catboost/decompress | source_build_screen | False | False | False | False | False |
| catboost/update_bins | source_build_screen | False | False | False | False | False |
| catboost/add_vector | source_build_screen | False | False | False | False | False |
| cuda-samples/incKernel | accepted_supplemental_sample_performance_target_failed | True | True | True | True | True |
| cupy/packbits | direct_edit_gpu_hot_rotating_timing_proof_frontend_blocked | True | True | True | False | False |
| cupy/unpackbits | direct_edit_gpu_hot_rotating_timing_proof_frontend_blocked | True | True | True | False | False |
| cupy/flatiter_getitem_slice | direct_edit_gpu_timed_frontend_blocked | True | True | False | False | False |
| cupy/flatiter_setitem_slice | direct_edit_gpu_timed_frontend_blocked | True | True | False | False | False |
| cupy/putmask | direct_edit_gpu_timed_frontend_blocked | True | True | False | False | False |
| cupy/resize | direct_edit_gpu_timed_frontend_blocked | True | True | False | False | False |
| cupy/tri | direct_edit_gpu_timed_frontend_blocked | True | True | False | False | False |
