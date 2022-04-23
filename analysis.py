import csv


def calculate_analysis(self):
    with open("analysis_TNF.csv", 'a') as f:
        w = csv.DictWriter(f, self.info.keys())
        #w.writeheader()
        w.writerow(self.info)
    #self.__write_csv(flines, len(self.formula), self.tnf_time, len(self.tnf_formula), self.short_tnf_time, len(self.short_tnf_res), self.dnf_tnf_verification, self.tnf_to_stnf_verification, "analysis_TNF.csv")

def __write_csv(self, f, DNF_len, TNF_Time, TNF_length, sTNF_time, sTNF_length, TNF_equal_DNF, sTNF_implies_TNF, path):

    row =  [f, DNF_len, TNF_Time, TNF_length, sTNF_time, sTNF_length, TNF_equal_DNF, sTNF_implies_TNF]
    # open the file in the write mode
    with open(path, mode='a') as f:
        writer = csv.writer(f, delimiter=',')
        # write a row to the csv file
        writer.writerow(row)

    # close the file
    f.close()
