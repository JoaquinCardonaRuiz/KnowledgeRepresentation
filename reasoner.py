from py4j.java_gateway import JavaGateway

gateway = JavaGateway()
parser = gateway.getOWLParser()
formatter = gateway.getSimpleDLFormatter()
print("Loading the ontology...")
ontology = parser.parseFile("sushi.owx")
gateway.convertToBinaryConjunctions(ontology)

tbox = ontology.tbox()
axioms = tbox.getAxioms()
allConcepts = ontology.getSubConcepts()

def find_concept(names):
    concepts = []
    for name in names:
        found = False
        for concept in allConcepts:
            if formatter.format(concept) == name:
                concepts.append(concept)
                found = True
        if not found:
            raise Exception(f'{name} not found')
    return concepts

class Graph:
    def __init__(self, init_concept_names):
        self.id_counter = 65
        init_concepts = find_concept(init_concept_names)
        self.population = {self.get_new_id(): Individual(con) for con in init_concepts}
        self.has_changed = True

    def get_new_id(self):
        id =  chr(self.id_counter)
        self.id_counter += 1
        return id    

    def reason(self):
        pass

    def print_graph(self):
        print('-'*25)
        for ind in self.population:
            self.population[ind].update_concepts()
            print(f'{ind}: {self.population[ind].format_concepts}')
        for ind in self.population:
            for r in self.population[ind].relations:
                print(f'{ind} --{r.role}--> {r.target}')

class Individual:
    def __init__(self, init_concept):
        self.relations = []
        self.concepts = [init_concept]
        self.format_concepts = []
        self.update_concepts()

    def update_concepts(self):
        self.format_concepts = [formatter.format(x) for x in self.concepts]

    def hasConcept(self,concept):
        return concept in self.concepts
    
    def __str__(self):
        return f'Individual {self.concepts}'


class Relation:
    def __init__(self, role, target):
        self.role = role
        self.target = target

    def __str__(self):
        return f'Role {self.role} --> {self.target}'


"""
Pseudocode:

while not_changed:
    for each axiom:
        if type == ⊑:
            add the rhs to every individual with the lhs
        if type = ≡:
            add the rhs to every individual with the lhs
            add the lhs to every individual with the rhs

    for each concept in each individual:
        if type == ∃r.:
            if a relation with the same role and valid target (with filler class) already exists:
                do nothing
            else:
                if a valid target individual already exists:
                    create relation from individual to target individual
                elif valid target individual exists in list of individuals to be created next loop:
                    create relation from individual to target (future) individual
                else:
                    add new individual to list of individuals to be created next loop
                    create relation from individual to target (future) individual
        if type == ⊓:
            if the components of the ⊓ are not already in the individual, and are in allConcepts:
                add the component to the individual
    
    for each new individual to be created:
        create the new individual in the population
        add the relevant relations to the population

    for each concept in allConcepts:
        if type == ⊓
            for every individual in the population:
                if all components of the concept are in the individual:
                    add the entire concept to the individual
               
"""

# Initialise the graph
graph = Graph(["CucumberRoll","PhiladelphiaRoll"])
# Index for # of steps, for logging
i=0
# We loop until we make no further changes to the graph
while graph.has_changed:
    graph.has_changed = False
    # We first loop through the ontologies axioms
    for axiom in axioms:
        axiomType = axiomType = axiom.getClass().getSimpleName() 
        # Inclusions
        if axiomType == 'GeneralConceptInclusion':
            for ind in graph.population:
                if axiom.lhs() in graph.population[ind].concepts and axiom.rhs() not in graph.population[ind].concepts:
                    graph.population[ind].concepts.append(axiom.rhs())
                    graph.has_changed = True
                    graph.population[ind].update_concepts()
        # Equivalences
        elif axiomType == 'EquivalenceAxiom':
            for concept in axiom.getConcepts():
                for ind in graph.population:
                    if concept in graph.population[ind].concepts:
                        for other_concept in axiom.getConcepts():
                            if other_concept not in graph.population[ind].concepts:
                                graph.population[ind].concepts.append(other_concept)
                                graph.has_changed = True

    new_inds = []
    # Then we loop through every concept in every individual
    for ind in graph.population: 
        for con in graph.population[ind].concepts:
            conceptType = con.getClass().getSimpleName()
            # Relations
            # If it's an existential role
            if(conceptType == "ExistentialRoleRestriction"):
                # Check that an identical relation doesn't already exist
                isObsolete = False
                # For every relation in the individual
                for relation in graph.population[ind].relations:
                    # If the filler is in the target
                    if relation.target not in graph.population.keys():
                        if relation.target not in [ind['id'] for ind in new_inds]:
                            raise Exception('Orphan Relation')
                    elif con.filler() in graph.population[relation.target].concepts and relation.role == con.role():
                        isObsolete = True
                # If it doesn't already exist, we check whether a new individual needs be created for it
                if not isObsolete:
                    # Check if individual with concept already exists
                    exists = False
                    for other_ind in graph.population:
                        if con.filler() in graph.population[other_ind].concepts:
                            exists = True
                            relation = Relation(con.role(),other_ind)
                            graph.population[ind].relations.append(relation)
                            graph.has_changed = True
                            break
                    # Elif, check if individual with concept is about to be created in the next loop
                    for new_ind in new_inds:
                        if con.filler() in new_ind['ind'].concepts:
                            exists = True
                            relation = Relation(con.role(),new_ind['id'])
                            graph.population[ind].relations.append(relation)
                            graph.has_changed = True
                    # Else, create a new individual
                    if not exists:
                        new_id = graph.get_new_id()
                        new_inds.append({'id':new_id,
                                         'ind':Individual(con.filler()),
                                         'relation': Relation(con.role(),new_id),
                                         'origin': ind})
            # Conjunctions in individuals
            elif(conceptType == "ConceptConjunction"):
                for conjunct in con.getConjuncts():
                    if conjunct not in graph.population[ind].concepts and conjunct in allConcepts:
                        graph.population[ind].concepts.append(conjunct)
                        graph.has_changed = True

    # Add new individuals, couldn't do before because we were looping through the individuals
    for new_ind in new_inds:
        graph.population[new_ind['id']] = new_ind['ind']
        graph.population[new_ind['origin']].relations.append(new_ind['relation'])
        graph.has_changed = True

    # Find conjunctions in topic
    for concept in allConcepts:
        conceptType = concept.getClass().getSimpleName()
        if conceptType == "ConceptConjunction":
            for ind in graph.population:
                if all([conjunct in graph.population[ind].concepts for conjunct in concept.getConjuncts()]) and concept not in graph.population[ind].concepts:
                    graph.population[ind].concepts.append(concept)
                    graph.has_changed = True

    # Print graph, next loop
    graph.print_graph()
    #_=input(f'Step {i} >>>')
    i+=1
