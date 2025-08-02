#!/usr/bin/env python3

import json
import sys

# get filename from first command line argument
filename = sys.argv[1]
data = {}
with open(filename, "r") as file:
    data = json.load(file)

top_module = sys.argv[2]

def rename(name):
    return name.replace("[", "_").replace("]", "").replace(".", "_")

new_modules = {}
for module in data['modules']:
    print(f"Renaming ports for module: {module}")
    new_ports = {}
    for port_name in data['modules'][module]['ports']:
        print(f"  Renaming port: {port_name}")
        port = data['modules'][module]['ports'][port_name]
        new_ports[rename(port_name)] = port

    new_cells = {}
    for cell_name in data['modules'][module]['cells']:
        print(f"Cell {cell_name} in module {module} has ports:")
        cell = data['modules'][module]['cells'][cell_name]
        
        if 'port_directions' in cell:
            new_port_directions = {}
            for port_name in cell['port_directions']:
                new_port_directions[rename(port_name)] = cell['port_directions'][port_name]
            cell['port_directions'] = new_port_directions
        

        if cell['type'] in data['modules']:
            cell['type'] = cell['type'] + "_gwsynth"

        new_cells[rename(cell_name)] = cell

        new_connections = {}
        for conn_name in cell['connections']:
            new_connections[rename(conn_name)] = cell['connections'][conn_name]
        cell['connections'] = new_connections

    data['modules'][module]['cells'] = new_cells

    new_netnames = {}
    for netname in data['modules'][module]['netnames']:
        new_netnames[rename(netname)] = data['modules'][module]['netnames'][netname]
    data['modules'][module]['netnames'] = new_netnames
    

    # print(f"  New ports: {new_ports}")
    data['modules'][module]['ports'] = new_ports

    new_module_name = module
    if module != top_module:
        new_module_name = module + "_gwsynth"
    new_modules[new_module_name] = data['modules'][module]

data['modules'] = new_modules

with open(filename, "w") as file:
    json.dump(data, file, indent=4)
print(f"Ports renamed and saved to {filename}")
