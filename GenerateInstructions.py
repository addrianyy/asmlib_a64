import re
from dataclasses import dataclass
from typing import Optional

prototype_re = re.compile(r"([\w\d|_@]+)\((.+)\)\s*({)?")


@dataclass
class Argument:
    type: str
    name: str
    default_value: Optional[str]


@dataclass
class Prototype:
    arguments: list[Argument]


@dataclass
class Instruction:
    name: str
    prototype: Prototype


processed_instructions: list[Instruction] = list()


class GlobalProcessor:
    def process(self, line: str):
        match = prototype_re.match(line)
        assert match is not None

        name = match.group(1)
        arguments = match.group(2).split(",")

        argument_list: list[Argument] = list()

        for argument in arguments:
            argument = argument.strip()
            default_value = None
            if "=" in argument:
                s = argument.split("=")
                assert len(s) == 2
                argument = s[0].strip()
                default_value = s[1].strip()

            s = argument.split()
            assert len(s) == 2
            argument_type = s[0].strip()
            argument_name = s[1].strip()

            argument_list.append(
                Argument(type=argument_type, name=argument_name, default_value=default_value))

        proto = Prototype(arguments=argument_list)

        if match.group(3) is not None:
            return PrototypeBlockProcessor(proto)
        else:
            processed_instructions.append(Instruction(name=name, prototype=proto))


class PrototypeBlockProcessor:
    def __init__(self, prototype: Prototype):
        self.prototype = prototype

    def process(self, line: str):
        if line == "}":
            return GlobalProcessor()
        else:
            processed_instructions.append(Instruction(name=line, prototype=self.prototype))


current_line_processor = GlobalProcessor()


def process_line(line: str):
    global current_line_processor
    new_processor = current_line_processor.process(line)
    if new_processor is not None:
        current_line_processor = new_processor


def write_cpp_function(output, prototype: Prototype, name: str, return_type: str):
    output.write(f"{return_type} {name}(")

    first = True
    for argument in prototype.arguments:
        if not first:
            output.write(", ")
        first = False

        output.write(f"{argument.type} {argument.name}")
        if argument.default_value:
            output.write(f" = {argument.default_value}")

    output.write(")")


with open("Instructions.def") as f:
    for line in f.readlines():
        stripped_line = line.strip()
        if len(stripped_line) > 0:
            process_line(stripped_line)

with open("src/asmlib_a64/Instructions.inc", "w") as f:
    for instruction in processed_instructions:
        write_cpp_function(f, instruction.prototype, f"try_{instruction.name}",
                           "[[nodiscard]] Status")
        f.write(";\n")

    f.write("\n\n")

    for instruction in processed_instructions:
        write_cpp_function(f, instruction.prototype, f"{instruction.name}", "void")
        f.write(" {\n")
        f.write(f"  const auto status = try_{instruction.name}(")

        first = True
        for argument in instruction.prototype.arguments:
            if not first:
                f.write(", ")
            first = False
            f.write(f"{argument.name}")
        f.write(");\n")
        f.write(f'  assert_instruction_encoded("{instruction.name}", status);\n')
        f.write("}\n")
