"""Emit resolution and contact certificates for nonsimplicial rank-seven cones outside E7.

Run with Sage's Python. The CaDiCaL and pycosat requirements are described in
watson_six_support.py. Supply a scratch directory for the DIMACS/LRAT data.
"""
import argparse
from pathlib import Path

from watson_seven_pivots import E7, read_forms
from watson_six_contact_tables import emit as emit_contacts
from watson_six_resolution import emit as emit_resolution
from watson_six_support import certify, cone_of_form


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('folder', type=Path)
    parser.add_argument('scratch', type=Path)
    parser.add_argument('--cadical', default='cadical')
    args = parser.parse_args()
    for k, (m, f) in enumerate(read_forms(args.folder)):
        if k == E7 or f.qfminim()[2].ncols() == 28:
            continue
        certify(k, args.cadical, args.scratch, cone_of_form(f, m))
        emit_resolution(k, args.scratch, args.folder, rank_name='Seven')
        emit_contacts(k, args.scratch, args.folder, rank=7)
