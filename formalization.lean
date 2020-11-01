
namespace emi

variables 
    {C : Type} -- configurations
    {A : Type} -- actions
    {L : Type} -- atomic propositions

-- STR structure
structure STR :=
    (initial : set C)
    (actions : C → set A) 
    (execute : C → A → set C)

-- Type to know if some actions are available or if there is a deadlock
universe u
inductive completed (α : Type u)
	| deadlock {} : completed
	| some    : α → completed

-- Operator used to complete a STR by adding implicit transitions
def add_implicit_transitions
    (str : @STR C A)
    [∀ c, decidable (str.actions c = ∅)]
: @STR C (completed A) := 
{ 
    initial := str.initial,
    actions := λ c, if str.actions c = ∅ then 
            (singleton completed.deadlock) 
        else 
            { oa | ∀ a ∈ str.actions c, oa = completed.some a }, 
    execute := λ c oa, match oa with
        | completed.deadlock  := singleton c
        | completed.some a := { oc | ∀ t ∈ str.execute c a, oc = t }
    end
}

-- Synchronous composition operator
def synchronous_composition (C₁ C₂ A₁ A₂ L₁ : Type)
    (lhs : @STR C₁ A₁)
    (eval₁ : L₁ → C₁ → A₁ → C₁ → bool)
    (rhs : @STR C₂ A₂)
    (eval₂ : C₂ → A₂ → L₁)
: @STR (C₁ × C₂) (A₁ × A₂) :=
{
    initial := { c | ∀ (c₁ ∈ lhs.initial) (c₂ ∈ rhs.initial), c = (c₁, c₂) },
    actions := λ c, { a | 
        match c with
        | (c₁, c₂) := ∀ (a₁ ∈ lhs.actions c₁) (a₂ ∈ rhs.actions c₂)
            (t₁ ∈ lhs.execute c₁ a₁) (t₂ ∈ rhs.execute c₂ a₂),
            match t₁, t₂ : ∀ t₁ t₂, Prop with 
            | t₁, t₂ :=  eval₁ (eval₂ c₂ a₂) c₁ a₁ t₁ = tt → a = (a₁, a₂)
            end
        end    
    },
    execute := λ c a, { t | 
        match c, a with 
        | (c₁, c₂), (a₁, a₂) :=  ∀ (t₁ ∈ lhs.execute c₁ a₁) 
        	(t₂ ∈ rhs.execute c₂ a₂), t = (t₁, t₂)
        end
    }  
}

end emi

