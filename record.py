import json


# reocrd 对象转json
def encode(record_list):
    with open("./record.json", 'w', encoding='utf-8') as f:
        f.write(json.dumps(record_list, indent=4, default=lambda obj: obj.__dict__))


def decode():
    with open("./record.json", 'r', encoding='utf-8') as f:
        str = f.read()
        records_dict = json.loads(str, object_hook=object_hook)
        return records_dict
        # list = []
        # for d in records_dict:
        #     record = Record(d['input_path'], d['start_time'], d['type'],d['out_path'], d['time'], d["result"])
        #     list.append(record)
        # return list


def object_hook(d):
    return Record(d['input_path'], d['start_time'], d['type'],d['out_path'], d['time'], d["result"])


class Record(object):
    def __init__(self):
        pass

    def __init__(self, input_path, start_time, type, out_path, time="", result=""):
        self.input_path = input_path
        self.start_time = start_time
        self.type = type
        self.time = time
        self.result = result
        self.out_path = out_path



# list = [Record("c:/", "1", "synthesis", "c:/"), Record("d:/", "2","synthesis", "d:/")]
# encode(list)

# #json转record对象
# list = decode()
# print(list)