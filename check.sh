echo -n "ZFC:       "
python3 nqlaconic.py --print-tm zf2.nql | wc -l
python3 nqlaconic.py --print-subs zf2.nql > output_zf2.txt
python3 assemble_blc.py loader 0 0
echo -n "Loader:    "
python3 nqlaconic.py --print-tm lam_loader.nql | wc -l
python3 nqlaconic.py --print-subs lam_loader.nql > output_loader.txt
python3 assemble_blc.py bms 0 1
echo -n "BLC BMS:   "
python3 nqlaconic.py --print-tm lam_bms.nql | wc -l
python3 nqlaconic.py --print-subs lam_bms.nql > output_bms.txt
echo -n "Direct BMS:"
python3 nqlaconic.py --print-tm bms.nql | wc -l
python3 nqlaconic.py --print-subs bms.nql > output_bms2.txt