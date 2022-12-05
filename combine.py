import pandas as pd
import numpy as np
import time
import os
import concurrent.futures
import itertools
import multiprocessing
from multiprocessing import Process
from strsimpy import SIFT4
from strsimpy.normalized_levenshtein import NormalizedLevenshtein
from strsimpy.damerau import Damerau
from strsimpy.levenshtein import Levenshtein
from strsimpy.normalized_levenshtein import NormalizedLevenshtein
from math import isnan
from strsimpy.metric_lcs import MetricLCS
from strsimpy.jaro_winkler import JaroWinkler
from strsimpy.longest_common_subsequence import LongestCommonSubsequence
from strsimpy.optimal_string_alignment import OptimalStringAlignment
from strsimpy.weighted_levenshtein import WeightedLevenshtein
from concurrent.futures import ProcessPoolExecutor
import random
import re
import csv
class transformation:
    def __init__(self,source,target,position_source,position_target,target_column_name):
        self.source=source
        self.target=target
        self.position_source=position_source
        self.position_target=position_target
        self.target_column_name=target_column_name
    def set_trans(self,source,target,position_source,position_target,target_column_name):
        self.source=source
        self.target=target
        self.position_source=position_source
        self.position_target=position_target
        self.target_column_name=target_column_name
    def print_trans(self):
        print("<",self.source , "--->", self.target,", " , self.position_source, ", ", self.position_target,">", "target colume name ",self.target_column_name)
    def get_target(self):
        return  self.target
def identical_transformation(transformation1,transformation2):
    if_identical=False
    if(transformation1.source==transformation2.source and transformation1.target==transformation2.target):
        if_identical=True
    return if_identical
def create_identity_transfomation(source_string,target_string,index,column_name):
    trans=transformation("","",-1,-1,"")
    x= source_string.find(target_string)
    target=target_string
    if(len(target)==1 and target.isdigit()):
        target=target.zfill(2)
    trans.set_trans(target,target,x,index,column_name)
    return trans
def generate_iden_set_rules(source,target,index,column_name,list_delimiter):
    #task()
    list=[]                                         
    for source_elem,target_elem in zip(source,target): # for every row of the examples
        print(target_elem)
        if(pd.notnull(target_elem)):
            for delimit_ele in list_delimiter:
                source_elem=source_elem.replace(delimit_ele," ")
            source_elem_split=source_elem.split()                            
            if(type(target_elem)==float):              # if type of the target column is float then convert it to string
                target_elem=int(target_elem)
                target_elem=str(target_elem)
            if(type(target_elem)==int):
                target_elem=str(target_elem)
            target_split=target_elem.split()

            if(len(target_split)==1):
                for source_elem_split_ele in source_elem_split:
                    if(target_elem==source_elem_split_ele):
                        trans=create_identity_transfomation(source_elem,target_elem,index,column_name) # create a transformation from the source string and target strng
                        if not list:                               # if list is empty
                            list.append(trans)
                            break
                        else:                                      # if list is not empty
                            check_identical=False                  
                            for elem_list in list:                 # check if the created transformation above has been added to the list
                                if(identical_transformation(elem_list,trans)==True):
                                    check_identical=True
                            if(check_identical==False):            # if not then add to list
                                list.append(trans)
                                break
            elif(len(target_split)>1):

                if(target_elem in source_elem):
                    trans=create_identity_transfomation(target_elem,target_elem,index,column_name) # create a transformation from the source string and target strng
                    if not list:                               # if list is empty
                        list.append(trans)
                    else:                                      # if list is not empty
                        check_identical=False                  
                        for elem_list in list:                 # check if the created transformation above has been added to the list
                            if(identical_transformation(elem_list,trans)==True):
                                check_identical=True
                        if(check_identical==False):            # if not then add to list
                            list.append(trans)
    return list
def helper(args):
    return generate_iden_set_rules(args[0],args[1],args[2],args[3],args[4])
def create_set_rules(dataframe,raw_column,handle_column,list_delimiter):
    list_return=[]
    example= dataframe[raw_column[0]]
    for col_elem in handle_column:
        list_col_return=generate_iden_set_rules(example,dataframe[col_elem],dataframe.columns.get_loc(col_elem),col_elem,list_delimiter)
        list_return.append(list_col_return)
    return list_return
def create_candidate_substring(source_column,set_of_identity_rules,list_column_splitting,df_example,list_delimiter):
    list_candidate=[]
    source=df_example[source_column[0]]
    x=0
    for source_ele in source:
        list_column_splitting_temp=[]
        for ele in list_column_splitting:
            list_column_splitting_temp.append(ele)
        for delimit_ele in list_delimiter:
            source_ele=source_ele.replace(delimit_ele," ")
        for identity_rules_column in set_of_identity_rules:
            for identity_rules_column_ele in identity_rules_column:
                if(identity_rules_column_ele.target in source_ele):
                    source_ele=source_ele.replace(identity_rules_column_ele.target,"")
                    column_name=str(identity_rules_column_ele.target_column_name)
                    list_column_splitting_temp.remove(column_name)
                    break
        source_temp=source_ele.split()
        if(len(list_column_splitting_temp)>0):
            for list_column_splitting_temp_ele in list_column_splitting_temp:
                column=df_example[list_column_splitting_temp_ele]
                if(pd.notnull(column[x])):
                    for source_split_ele in source_temp:
                        trans= transformation(source_split_ele,column[x],0,df_example.columns.get_loc(list_column_splitting_temp_ele),list_column_splitting_temp_ele)
                        list_candidate.append(trans)
        x=x+1
    return list_candidate

def FindBestAlignment(set_of_rules, string_1,string_2):
    Aligment=[]
    for column_ele in set_of_rules:
        for ele in column_ele:
            if(ele.source in string_1 and ele.target in string_2):
                Aligment.append(ele)
    return Aligment
def GenCandRuleAppl(source_column,set_of_identity_rules,list_column_splitting,df_example,list_delimiter,index):
    Candidate=[]
    list_column_splitting_temp=[]
    source=df_example[source_column[0]]
    source_ele=source[index]
    for ele in list_column_splitting:
        list_column_splitting_temp.append(ele)
    for delimit_ele in list_delimiter:
        source_ele=source_ele.replace(delimit_ele," ")
    for identity_rules_column in set_of_identity_rules:
        for identity_rules_column_ele in identity_rules_column:
            if(identity_rules_column_ele.target in source_ele):
                source_ele=source_ele.replace(identity_rules_column_ele.target,"")
                column_name=str(identity_rules_column_ele.target_column_name)
                list_column_splitting_temp.remove(column_name)
                break
    source_temp=source_ele.split()
    if(len(list_column_splitting_temp)>0):
        for list_column_splitting_temp_ele in list_column_splitting_temp:
            column=df_example[list_column_splitting_temp_ele]
            if(pd.notnull(column[index])):
                for source_split_ele in source_temp:
                    trans= transformation(source_split_ele,column[index],0,df_example.columns.get_loc(list_column_splitting_temp_ele),list_column_splitting_temp_ele)
                    Candidate.append(trans)
    return Candidate

def Coverage(aligment):
    total =0
    for ele in aligment:
        target_split=ele.target.split()
        source_split=ele.source.split()
        total =total + len(target_split) + len(source_split)
    return total

def CovTotal(list_aligment):
    total=0
    for ele in list_aligment:
        total=total+Coverage(ele)
    return total

def Sup(r,list_candidate):
    total=0
    for list_ele in list_candidate:
        for ele in list_ele:
            if(ele.target==r.target and ele.source==r.source ):
                target_split=ele.target.split()
                source_split=ele.source.split()
                total=total+len(target_split)+ len(source_split) 
    return total

def FindBestRule(list_candidate):
    #list_of_unidentical_candidate=[]
    bestrule=transformation("","",-1,-1,"")
    best=0
    for each in list_candidate:
        for ele in each:
            if bestrule.position_source==-1:
                bestrule=ele
                best=Sup(ele,list_candidate)
            else:
                temp=Sup(ele,list_candidate)
                if(temp>best):
                    bestrule=ele
                    best=temp
    return bestrule
    
def UpdateAlignment(aligment, r):
    aligment.append(r)
    return aligment      
def FindOverlapRuleAppl(r,list_candidate):
    list_overlap_rule=[]
    for each in list_candidate:
        for ele in each:
            if(ele.source==r.source or ele.target==r.source or ele.source==r.target or ele.target==r.target):
                list_overlap_rule.append(ele)
    return list_overlap_rule
def greedy_algorithm(df_example,prior_collection, k,source_column,list_column_splitting,list_delimiter):
    list_aligment=[]
    list_candidate=[]
    list_rule=[]
    list_aligment=prior_collection
    for index in range(len(df_example)):
        candidate= GenCandRuleAppl(source_column,prior_collection,list_column_splitting,df_example,list_delimiter,index)
        list_candidate.append(candidate)
    for i in range(k):
        r= FindBestRule(list_candidate)
        if(r.position_source!=-1):
            if not list_rule:
                list_rule.append(r)
                list_aligment.append(list_rule)
            else:
                len_list=len(list_aligment)
                list_aligment.remove(list_aligment[len_list-1])
                list_rule.append(r)
                list_aligment.append(list_rule)
            list_overlap=FindOverlapRuleAppl(r,list_candidate)
            for ele in list_overlap:
                for candidate_ele in list_candidate:
                    for candidate_ele_ele in candidate_ele:
                        if(ele.target==candidate_ele_ele.target and ele.source==candidate_ele_ele.source):
                            candidate_ele.remove(candidate_ele_ele)
                            break
        #list_candidate_temp=[]
        # for index in range(N):
        #     list_candidate_temp=[]
        #     list_aligment[index]=UpdateAlignment(list_aligment[index], r)
        #     list_overlap_rule= FindOverlapRuleAppl(list_candidate[index],list_aligment[index])
        #     for candidate_ele in list_candidate[index]:
        #         identical=False
        #         for list_overlap_rule_ele in list_overlap_rule:
        #             if(identical_transformation(candidate_ele,list_overlap_rule_ele)):
        #                 identical=True
        #                 break
        #         if(identical==False):
        #             list_candidate_temp.append(candidate_ele)
        #     list_candidate[index]=list_candidate_temp
    return list_aligment


def substitution_cost(char_a, char_b):
    if (char_a.isalpha() and char_b.isdigit()):
        return 2
    elif(char_a.isdigit() and char_b.isalpha()):
        return 2
    if(char_a.isdigit() and char_b.isdigit()):
        return 0.5
    else:
        return 1.0

def calculate_minimum_pairwise(input,column,index,dict):
    #task()
    #damerau = Damerau()
    #damerau = Levenshtein()
    #damerau =NormalizedLevenshtein()
    #damerau =MetricLCS()
    #damerau= LongestCommonSubsequence()
    #damerau= OptimalStringAlignment()
    damerau = WeightedLevenshtein(substitution_cost_fn=substitution_cost)
    similar_string=""
    list_return=[]
    minimum=100
    # for elem in column:
    #         if(pd.notnull(elem)):
    #             if(input in str(elem) and input.isnumeric()==False ):
    #                 minimum=0
    #                 similar_string=elem
    #                 break
    #             else:
    #                 if(damerau.distance(input,str(elem))<minimum):
    #                     minimum=damerau.distance(input,str(elem))
    #                     similar_string=elem
    if(input[0] in dict):
        for elem in dict[input[0]]:
            if(pd.notnull(elem)):
                if(input in str(elem) and input.isdigit()==False):
                    minimum=0
                    similar_string=elem
                    break
                else:
                    if(damerau.distance(input,str(elem))<minimum):
                        minimum=damerau.distance(input,str(elem))
                        similar_string=elem
    else:
        for elem in column:
            if(pd.notnull(elem)):
                if(input in str(elem) and input.isdigit()==False):
                    minimum=0
                    similar_string=elem
                    break
                else:
                    if(damerau.distance(input,str(elem))<minimum):
                        minimum=damerau.distance(input,str(elem))
                        similar_string=elem
    list_return.append(column.name)
    list_return.append(minimum)
    list_return.append(input)
    list_return.append(index)
    list_return.append(similar_string)
    return list_return
def helper_calculate(args):
    return calculate_minimum_pairwise(args[0],args[1],args[2])
def takeSecond(elem):
    return elem[1]

def find_best_fit(input,list_column_null,index,dataframe,df_example_dict):
    #task()
    list_column=[]
    list_manager=[]
    for column in list_column_null:
        list_column.append(dataframe[column])
    list_results=[]
    for column in list_column:
        list_manager.append(calculate_minimum_pairwise(input,column,index,df_example_dict[column.name][0]))
    list_manager.sort(key=takeSecond)
    print(list_manager)
    if(len(list_manager)>0):
        return list_manager[0]
    elif(len(list_manager)==0):
        print("problem at ", index)
        return list_manager
def helper_find_best(args):
    return find_best_fit(args[0],args[1],args[2],args[3],args[4])
def record_matching_column(list_manager,set_rules,raw_data,delimiter_list):
    for elem_data in raw_data:
        for ele in delimiter_list:
            elem_data=elem_data.replace(ele," ")
        elem_data_split=elem_data.split()
        track=0
        for rule_elem in set_rules:
            if(rule_elem.source in elem_data_split):
                list_manager.append(rule_elem.target)
                break
            elif(rule_elem.source not in elem_data_split and track==len(set_rules)-1):
                list_manager.append(np.nan)
            track=track+1
    return list_manager

def helper_record(args):
    return record_matching_column(args[0],args[1],args[2],args[3])

def split_string(input):
    string_split= input.split()
    list_return= []
    string_temp=[]
    flag=0
    for ele in string_split:
        if(ele=="&" and flag != len(string_split)-1):
            if(len(string_temp)>0):
                list_return.append(' '.join(string_temp))

            string_temp=[]
        elif(ele=="&" and flag == len(string_split)-1):
            if(len(string_temp)>0):
                list_return.append(' '.join(string_temp))
            break
        elif(ele!="&" and flag != len(string_split)-1):
            string_temp.append(ele) 
        elif(ele!="&" and flag == len(string_split)-1):
            string_temp.append(ele) 
            list_return.append(' '.join(string_temp))
            break
        flag+=1
    return list_return


def find_best_fit_for_string(raw_data_string,list_column_null,index,dataframe,df_example_dict):
    list_return=[]
    print("index is ",index)
    raw_data_string_split= split_string(raw_data_string)
    print(raw_data_string_split)
    for ele in raw_data_string_split:
        split_raw_data=ele.split()
        for x in range(len(split_raw_data)):
            forward=1
            backward=-1
            best_fit=find_best_fit(split_raw_data[x],list_column_null,index,dataframe,df_example_dict)
            disable_left=False
            disable_right=False
            token=split_raw_data[x]
            while(True):
                if(x==0):
                    if(x+forward<len(split_raw_data)):
                        hold=[]
                        hold.append(token)
                        hold.append(split_raw_data[x+forward])
                        string =" ".join(hold)
                        check_right=find_best_fit(string,list_column_null,index,dataframe,df_example_dict)
                        if(check_right[1]<= best_fit[1]):
                            token=string
                            forward= forward+1
                            best_fit=check_right
                        else:
                            break
                    else:
                        break
                elif(x==len(split_raw_data)-1):
                    if(x+backward>-1):
                        hold=[]
                        hold.append(token)
                        hold.append(split_raw_data[x+backward])
                        string =" ".join(hold)
                        check_left=find_best_fit(string,list_column_null,index,dataframe,df_example_dict)
                        if(check_left[1]<= best_fit[1]):
                            token=string
                            backward= backward-1
                            best_fit=check_left
                        else:
                            break
                    else:
                        break
                elif(x>0 and x<len(split_raw_data)-1):
                    if(disable_left==False and disable_right==False and x+forward<len(split_raw_data) and x+backward>-1):
                        hold_left=[]
                        hold_left.append(token)
                        hold_left.append(split_raw_data[x+backward])
                        string_left =" ".join(hold_left)
                        hold_right=[]
                        hold_right.append(token)
                        hold_right.append(split_raw_data[x+forward])
                        string_right =" ".join(hold_right)
                        check_right=find_best_fit(string_right,list_column_null,index,dataframe,df_example_dict)
                        check_left=find_best_fit(string_left,list_column_null,index,dataframe,df_example_dict)
                        if(check_right[1]<=check_left[1]):
                            disable_left=True
                            if(check_right[1]<= best_fit[1]):
                                token=string_right
                                forward= forward+1
                                best_fit=check_right
                            else:
                                break
                        elif(check_right[1]>check_left[1]):
                            disable_right=True
                            if(check_left[1]<= best_fit[1]):
                                token=string_left
                                backward= backward-1
                                best_fit=check_left
                            else:
                                break
                    elif(disable_left==True and disable_right==False):
                        if(x+forward<len(split_raw_data)):
                            hold=[]
                            hold.append(token)
                            hold.append(split_raw_data[x+forward])
                            string =" ".join(hold)
                            check_right=find_best_fit(string,list_column_null,index,dataframe,df_example_dict)
                            if(check_right[1]<= best_fit[1]):
                                token=string
                                forward= forward+1
                                best_fit=check_right
                            else:
                                break
                        else:
                            break
                    elif(disable_left==False and disable_right==True):
                        if(x+backward>-1):
                            hold=[]
                            hold.append(token)
                            hold.append(split_raw_data[x+backward])
                            string =" ".join(hold)
                            check_left=find_best_fit(string,list_column_null,index,dataframe,df_example_dict)
                            if(check_left[1]<= best_fit[1]):
                                token=string
                                backward= backward-1
                                best_fit=check_left
                            else:
                                break
                        else:
                            break
            if(len(list_return)>0):
                last=list_return[len(list_return)-1]
                if(last[0]==best_fit[0] and (best_fit[2] not in last[2] )):
                    combine=[]
                    combine.append(last[2])
                    combine.append(best_fit[2])
                    combine_string=" ".join(combine)
                    list_return[len(list_return)-1][2]=combine_string
                elif(last[0]!=best_fit[0]):
                    list_return.append(best_fit)
            else:
                list_return.append(best_fit)
    print(list_return)
    return list_return
def handle_after_record(new_data,df_example,delimiter_list,raw_data,index,column_splitted,df_example_dict):
    list_manager1=[]
    list_manager2=[]
    list_return=[]
    raw_data_string=raw_data[index]
    list_column_null=[]
    for delimit_ele in delimiter_list:
        raw_data_string=raw_data_string.replace(delimit_ele," ")
    raw_data_string_split=raw_data_string.split()
    for column in column_splitted:
        if(pd.notnull(new_data.at[index,column])):
            for x in range(len(raw_data_string_split)):
                if(new_data.at[index,column]== raw_data_string_split[x]):
                    raw_data_string_split[x]="&"
        elif(pd.isnull(new_data.at[index,column])):
            list_column_null.append(column)
    raw_data_string=" ".join(raw_data_string_split)
    print(raw_data_string)
    list_return=find_best_fit_for_string(raw_data_string,list_column_null,index,df_example,df_example_dict)
    return list_return
def helper_handle_after_record(args):
    return handle_after_record(args[0],args[1],args[2],args[3],args[4],args[5],args[6])
def record_matching(set_rules,raw_dataframe,raw_column, name_of_source_column,all_need_to_split,need_to_split,delimiter_list,df_example,df_example_dict):
    with ProcessPoolExecutor(max_workers=64) as executor:
        start= time.perf_counter()
        new_data=pd.DataFrame()
        
        # for column in raw_column:
        #     new_data[column]=  raw_dataframe[column]                 
        #     new_data=new_data.astype({column: 'object'})
        for column in all_need_to_split:
            new_data[column]=np.nan
            new_data=new_data.astype({column: 'object'})
        for column in raw_column:
            new_data[column]=  raw_dataframe[column]                 
            new_data=new_data.astype({column: 'object'})
        raw_data=raw_dataframe[name_of_source_column]
        args=((list_manager,set_rule_ele,raw_data,delimiter_list) for set_rule_ele in set_rules)
        list_manager = []
        results=executor.map(helper_record,args)
        list_results = list(results)
        for name,list_column in zip(need_to_split,list_results):
            if(len(list_column)>0):
                new_data[name] = list_column
        args1=((new_data,df_example,delimiter_list,raw_data,index,all_need_to_split,df_example_dict) for index in new_data.index)
        results1= executor.map(helper_handle_after_record,args1)
        results1=list(results1)
        flag=0
        for each_row in results1:
            each_row_temp=each_row
            print(each_row)
            count=len(each_row_temp)
            while(count>0):
                handle_after=[]
                for each_column in each_row_temp:
                    if(pd.isnull(new_data.at[flag,each_column[0]])):
                        new_data.at[flag,each_column[0]]=each_column[2]
                        count=count-1
                    elif(pd.notnull(new_data.at[flag,each_column[0]])):
                        for each_column_small in each_row:
                            if(each_column_small != each_column and each_column_small[0]==each_column[0]):
                                if(each_column_small[1]>each_column[1]):
                                    new_data.at[flag,each_column[0]]=each_column[2]
                                    handle_after.append(each_column_small)
                                    break
                                elif(each_column_small[1]<=each_column[1]):
                                    handle_after.append(each_column)
                                    break   
                print("handle after list = ", handle_after)
                column_null=[]
                for column in new_data.columns:
                        if(pd.isnull(new_data.at[flag,column]) and new_data[column].count()>0):
                            column_null.append(column)
                if(len(handle_after)==1 and len(column_null)>0):
                    for column in new_data.columns:
                        if(pd.isnull(new_data.at[flag,column]) and new_data[column].count()>0):
                            temp=handle_after[0]
                            new_data.at[flag,column]=temp[2]
                            count=count-1
                            break
                elif(len(handle_after)>1 and len(column_null)>0):
                    manager1=[]
                    manager3=[]
                    for handle_after_ele in handle_after:
                        manager1.append(find_best_fit(handle_after_ele[2],column_null,flag,df_example,df_example_dict))
                    manager3=manager1
                    print("best fit recalculate = ", manager3)
                    each_row_temp=manager3
                elif(len(handle_after)==1 and len(column_null)==0):
                    
                    for x in range(len(each_row_temp)):
                        if(each_row_temp[x]==handle_after[0]):
                            hold_temp=[]

                            if(x==0):
                                hold_temp.append(each_row_temp[x][2])
                                hold_temp.append(each_row_temp[x+1][2])
                                new_data.at[flag,each_row_temp[x+1][0]]=' '.join(hold_temp)
                            elif(x==len(each_row_temp)-1):
                                hold_temp.append(each_row_temp[x][2])
                                hold_temp.append(each_row_temp[x-1][2])
                                new_data.at[flag,each_row_temp[x-1][0]]=' '.join(hold_temp)
                            else:
                                list_column_left_temp=[]
                                list_column_left_temp.append(each_row_temp[x-1][0])
                                list_column_right_temp=[]
                                list_column_right_temp.append(each_row_temp[x+1][0])
                                check_right=find_best_fit(each_row_temp[x][2],list_column_right_temp,each_row_temp[x+1][3],df_example,df_example_dict)
                                check_left=find_best_fit(each_row_temp[x][2],list_column_left_temp,each_row_temp[x-1][3],df_example,df_example_dict)
                                
                                if(check_right[2]<=check_left[2]):
                                    hold_temp.append(each_row_temp[x][2])
                                    hold_temp.append(each_row_temp[x+1][2])
                                    new_data.at[flag,each_row_temp[x+1][0]]=' '.join(hold_temp)
                                else:
                                    hold_temp.append(each_row_temp[x][2])
                                    hold_temp.append(each_row_temp[x-1][2])
                                    new_data.at[flag,each_row_temp[x-1][0]]=' '.join(hold_temp)

                    break
                else:
                    print("case no column left ",handle_after)
                    break
            flag=flag+1
        finish= time.perf_counter()
        print(f'Finished in {finish-start} second')
        return new_data
def auto_find_source(list_column_splitted,list_column_raw,data):
    damerau = Damerau()
    splitted_string1=[]
    minimum=100
    similar_column=""
    for column in list_column_splitted:
        temp=data[column]
        splitted_string1.append(str(temp[0]))
    splitted_string=' '.join(splitted_string1)
    for column in list_column_raw:
        temp=data[column]
        min=damerau.distance(temp[0],splitted_string)
        if(min<minimum):
            minimum=min
            similar_column=column
    return similar_column

def find_delimiter(df_example,source_column,splitted_column):
    list_delimiter=[]
    raw=df_example[source_column]
    #first_raw=raw[0]
    #print(first_raw)
    for t in range(len(raw)):
        first_raw=raw[t]
        for column in splitted_column:
            delimiter=""
            split=df_example[column]
            if(pd.notnull(split[t])):
                string_split=str(split[t])
                x=first_raw.find(string_split)
                if(x+len(string_split)<len(first_raw)):
                    delimiter= first_raw[x+len(string_split)]
                if (delimiter not in list_delimiter and delimiter.isdigit()==False and delimiter!="" and delimiter.isalpha()==False):
                    list_delimiter.append(delimiter)
                    print("add:", delimiter)
                    print(first_raw)
    return list_delimiter
    


if __name__ == '__main__':
    
    with multiprocessing.Manager() as manager:
        start= time.perf_counter()

        #example="C:/Users/hoang/bachelor/upload/data/messages_datetime_mix.csv"
        #need_to_split="C:/Users/hoang/bachelor/upload/data/messages_datetime_raw.csv"
        #example="C:/Users/hoang/bachelor/upload/data/messages_datetime_mix.csv"
        example="belgium_detail_mix.csv"
        need_to_split="belgium_detail_raw.csv"

        #list_column_splitting1=["year","month","day","time"]
        
        list_column_splitting1=["CITY","REGION","POSTCODE","COUNTRY"]
        # # example="C:/Users/hoang/bachelor/upload/data/reference.csv"
        # # need_to_split="C:/Users/hoang/bachelor/upload/data/reference_raw.csv"
        # # list_column_splitting1=['author','year','title','journal','doi']
        # # example="data/belgium_detail_mix.csv"
        # # need_to_split="data/belgium_detail_raw.csv"
        
        
        number_raw_string=1000000
        raw_string_in_piece=5000
        process_time=number_raw_string/raw_string_in_piece
        list_number_raw_string=[]
        for x in range(int(process_time)+1):
            list_number_raw_string.append(raw_string_in_piece*x)
        df_raw=pd.read_csv(need_to_split)
        df_example=pd.read_csv("belgium_detail_800_sample.csv")
        df_example=df_example.reset_index(drop=True)
        for column_example in df_example.columns:
            if(df_example[column_example].dtypes==np.float64):
                df_example[column_example]=df_example[column_example].astype("Int64")
                df_example[column_example]=df_example[column_example].astype("object")
            elif(df_example[column_example].dtypes==np.int64):
                df_example[column_example]=df_example[column_example].astype("object")
        df_todict=df_example.to_dict()
        df_example_dict={}
        for ele in df_todict:
            df_example_dict[ele]=[]
            df_dict_temp={}
            for x in range(len(df_todict[ele])):
                if(pd.isna(df_todict[ele][x]) == False ):
                    if(type(df_todict[ele][x]) is not str):
                        df_todict[ele][x]=str(df_todict[ele][x])
                    if df_todict[ele][x][0] not in df_dict_temp.keys():
                        df_dict_temp[df_todict[ele][x][0]] = []
                        df_dict_temp[df_todict[ele][x][0]].append(df_todict[ele][x])
                    else:
                        if df_todict[ele][x] not in df_dict_temp[df_todict[ele][x][0]]:
                            df_dict_temp[df_todict[ele][x][0]].append(df_todict[ele][x])
            df_example_dict[ele].append(df_dict_temp)
        column_raw= []
        list_column_splitting=[]
        for column_example in df_example.columns:
            if(column_example in df_raw):
                column_raw.append(column_example)
            elif(column_example not in df_raw):
                list_column_splitting.append(column_example)
        name_of_source_column=auto_find_source(list_column_splitting,column_raw,df_example)
        list_delimiter= find_delimiter(df_example,name_of_source_column, list_column_splitting)
        source_column=[name_of_source_column]
        list_return= create_set_rules(df_example,source_column,list_column_splitting1,list_delimiter)
        list_return=list(list_return)
        list_return=greedy_algorithm(df_example,list_return,1,source_column,list_column_splitting1,list_delimiter)
        hold_dataframe=[]
        total_time=0
        for x in range(int(process_time)):
            print("processing ",(x/process_time)*100,"%")
            df_raw1= df_raw.loc[list_number_raw_string[x]:list_number_raw_string[x+1]-1]
            df_raw1=df_raw1.reset_index(drop=True)
            print(df_raw1)
            start1= time.perf_counter()
            new_data_temp= record_matching(list_return,df_raw1,column_raw, name_of_source_column,list_column_splitting,list_column_splitting1,list_delimiter,df_example,df_example_dict)
            finish1= time.perf_counter()
            total_time= total_time+(finish1-start1)
            hold_dataframe.append(new_data_temp)
            print("#----------------------------------------------------------#")
        new_data=pd.concat(hold_dataframe)
        new_data=new_data.reset_index(drop=True)
        #new_data.to_csv("messages_datetime.csv")
        print(new_data)
        #new_data.to_csv("belgium_detail_result_2.csv", index=False)
        df_correct=pd.read_csv(example)
        df_correct=df_correct.iloc[0:1000000]
        df_correct=df_correct.reset_index(drop=True)
        for column_example in df_correct.columns:
            if(df_correct[column_example].dtypes==np.float64 and df_correct[column_example].count()>0):
                df_correct[column_example]=df_correct[column_example].astype("Int64")
                df_correct[column_example]=df_correct[column_example].astype("string")
                df_correct[column_example]=df_correct[column_example].astype("object")
            elif(df_correct[column_example].dtypes==np.int64):
                df_correct[column_example]=df_correct[column_example].astype("string")
                df_correct[column_example]=df_correct[column_example].astype("object")
        df_compare=new_data.compare(df_correct)
        #df_compare.to_csv("belgium_detail_false.csv", index=False)
        print(df_compare.to_string())
        print("number example: ", len(df_example.index))
        print("number of raw string: ", number_raw_string)
        print("number of row each process: ",raw_string_in_piece )
        print("the percent of correct splitted: ",100-((len(df_compare.index)/len(df_correct))*100) , "%")            
        finish= time.perf_counter()
        print(f'Finished in {finish-start} seconds')
        #average_time= ((finish-start)/process_time)
        print("average process time for each ",raw_string_in_piece," rows is ",(total_time/process_time)," seconds") 


    
