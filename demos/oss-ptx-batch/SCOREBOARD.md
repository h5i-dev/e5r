# Practical OSS PTX batch scoreboard

Target: approximately 50 distinct real OSS kernels. Practical totals: {'optimization_attempt': 7, 'gpu_tested': 7, 'fair_timing': 2, 'proof_attempt': 0, 'strict_accepted': 0, 'accepted_win': 0}.

Source/build screens do not count as optimization or proof attempts. A direct edit alone does not count as a completed attempt. Strict acceptance requires the exact bound programs, direct universal equivalence, safety/races/progress/frame, replay, axiom audit and negatives. Timing wins require normal and strongest applicable baseline evidence.

| Kernel | Phase | Edited | GPU | Fair timing | Proof attempted | Strict accepted |
| --- | --- | --- | --- | --- | --- | --- |
| catboost/make_sequence | source_build_screen | False | False | False | False | False |
| catboost/fill_buffer | source_build_screen | False | False | False | False | False |
| catboost/inverse_permutation | source_build_screen | False | False | False | False | False |
| catboost/reverse | direct_edit_gpu_extracted_timing_full_TU_and_proof_pending | True | True | False | False | False |
| catboost/gather_mask | source_build_screen | False | False | False | False | False |
| catboost/zero_segments | direct_edit_gpu_extracted_timing_full_TU_and_proof_pending | True | True | False | False | False |
| catboost/zero_partitions | direct_edit_gpu_extracted_timing_full_TU_and_proof_pending | True | True | False | False | False |
| catboost/update_partition_sizes | source_build_screen | False | False | False | False | False |
| catboost/fill_query_end_mask | direct_edit_gpu_extracted_timing_full_TU_and_proof_pending | True | True | False | False | False |
| catboost/compute_group_ids | direct_edit_gpu_extracted_timing_full_TU_and_proof_pending | True | True | False | False | False |
| catboost/compress | source_build_screen | False | False | False | False | False |
| catboost/decompress | source_build_screen | False | False | False | False | False |
| catboost/update_bins | source_build_screen | False | False | False | False | False |
| catboost/add_vector | source_build_screen | False | False | False | False | False |
| cuda-samples/incKernel | accepted_supplemental_sample_performance_target_failed | True | True | True | True | True |
| cupy/packbits | direct_edit_gpu_hot_rotating_timing_proof_frontend_blocked | True | True | True | False | False |
| cupy/unpackbits | direct_edit_gpu_hot_rotating_timing_proof_frontend_blocked | True | True | True | False | False |
