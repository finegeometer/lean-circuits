# Circuits

This project attempts to formalize the concept of an electronic circuit.
Starting at the level of raw voltages and currents, I hope to abstract upwards
towards logic gates and digital logic.

The near-term goal is to define what it means for a collection of transistors to implement a piece of combinational logic, then set up a compositional way to prove this
for specific circuits.

## Tour

Here's a guide to the files in the project.
- **Utils**: Basic mathematical concepts, such as pushouts or cospans.
    Basically anything that could have been in Mathlib, but isn't.
- **Kirchhoff**: Deals with circuits that consist purely of wires.
    Connects the abstract description as a cospan over the sets of terminals
    to the concrete relationships between the voltages and currents.
    The proof that composition of cospans matches composition of voltage-current relations is particularly complicated.
- **Circuit**: A description of the behavior of a circuit, as a relation on the voltages and currents at its terminals.
- **Network**: An abstract network, consisting of a number of components that have been wired together.
- **Interp**: The relationship between abstract networks and concerete circuits.
- **Component**: Basic electrical components, such as resistors, capacitors, inductors, and transistors.

