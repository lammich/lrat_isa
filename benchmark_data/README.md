# Benchmark data

The raw log data from our benchmark runs, and some data extracted from it, in key-value and csv format.
The csv format contains a few derived fields like ratios and combined user+system time,
that are not part of the (raw) kv-data.

The benchmarks have been performed on our machine "two":
  * OS: Ubuntu 22.04 (64-bit)
  * CPU: AMD Ryzen 9 7950X3D @ 4.2-5.7 GHz (16 cores x 2 threads, with AVX-512)
  * RAM: 128 GB DDR5
  * Storage:
    * 0.5 TB Samsung 970 EVO Plus (NVMe, PCIe 3.0) - OS and /home
    * 2.0 TB Samsung 990 Pro SSD  (NVMe, PCIe 4.0) - /ssd


Note that streaming mode is called online mode in this data, and
our lrat_isa tool is called lrat_checker or lrat_llvm in this data.
For example, the key "test_lrat_llvm_online/lrat_checker/mrs_size" is the maximum resident set size of our lrat_isa tool, during the lrat_llvm_online test.

Also note that the mrs_size fields obtained by the time commands for the parallel runs seem not be accurate. We have not used these fields for our evaluation. The raw logging data also contains more accurate measurements obtained by runlim.

Here are the meanings of the keys:
  * test_download: dummy to ensure problem was downloaded
  * test_gen_lrat: dummy to ensure certificate files were present

  * test_baseline: cadical without certificate generation
  * test_gen_lrat: cadical and writes the certificate to a file

  * test_lrat_llvm_online: cadical and lrat_checker (aka lrat-isa) in streaming mode
  * test_cake_online: cadical and cake_lpr in streaming mode

  * bcake_xxx_ratio: ratios of value xxx for cake_lpr vs. cadical without certificate generation
  * fcake_xxx_ratio: ratios of value xxx for cake_lpr vs. cadical writing certificate to file
  * blrat_xxx_ratio: ratios of value xxx for lrat_isa vs. cadical without certificate generation
  * flrat_xxx_ratio: ratios of value xxx for lrat_isa vs. cadical writing certificate to file

  * test_notrim_xxx / test_trim_xxx: checker xxx run on original / trimmed certificate. There are various subkeys indicating how the certificate was generated from the original binary encoded lrat file. They are not included in the derived ratio-fields, or in the reported times in the paper.
  The checkers are:
    * lrat_checker: Our tool, aka lrat_isa
    * trim: The lrat-trim tool in forward mode
    * lchk: The lrat-check tool that comes with drat-trim
    * gratchk: The gratchk tool
    * cake: cake_lpr
    * acl2: The acl2 based lrat checker




