import csv


def calculate_analysis(info):

    with open("analysis_TNF.csv", 'r') as f:
        if not f.readlines():
            include_header = True
        else:
            include_header = False
    f.close()

    with open("analysis_TNF.csv", 'a') as f:
        w = csv.DictWriter(f, info.keys())
        if include_header:
            w.writeheader()
        w.writerow(info)
    f.close()

