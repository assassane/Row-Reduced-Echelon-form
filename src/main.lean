import linear_algebra.determinant tactic.ring tactic.linarith data.matrix.pequiv data.matrix.notation
import tactic.unfold_cases

universes u u' v w
variables {m n : ℕ} {l o p: Type*} [fintype l] [fintype o] [fintype p]
variables {α : Type v} [field α]
-- variables {M N : matrix m n α}




open matrix

localized "infixl ` ⬝ `:75 := matrix.mul" in matrix


-- a*Rᵢ+b*Rⱼ → Rᵢ 
def row_add_linear [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) (a b : α) :
  matrix l o α :=
update_row M i₁ (λ c,a • M i₁ c + b • M i₂ c)



lemma row_add_linear_ite [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) (a b : α): 
  row_add_linear M i₁ i₂ a b = (λ i j,if i = i₁  then a * M i₁ j + b * M i₂ j else M i j) := 
by ext i j;simp [row_add_linear];by_cases h_:i = i₁;simp [h_]

lemma testt [decidable_eq l] {M : matrix l o α} {X : matrix o p α} {B : matrix l p α}
  (i₁ i₂: l) (a b : α) : M ⬝ X = B → (row_add_linear M i₁ i₂ a b) ⬝ X = (row_add_linear B i₁ i₂ a b) :=
begin
intro h,
ext i j,
simp [row_add_linear_ite,row_add_linear_ite,matrix.mul],
by_cases hh:i = i₁;simp [hh],
{
  have h_i₁:=ext_iff.2 h i₁ j,
  have h_i₂:=ext_iff.2 h i₂ j,
  simp [matrix.mul] at h_i₁, simp [matrix.mul] at h_i₂,
  rw [←h_i₁,←h_i₂,←smul_dot_product,←smul_dot_product,←add_dot_product],
  have h_h:(λ j_1, a * M i₁ j_1 + b * M i₂ j_1) = a • M i₁ + b • M i₂,from rfl,
  rw [h_h]
},
exact ext_iff.2 h i j
end


lemma testt_iff [decidable_eq l] {M : matrix l o α} {X : matrix o p α} {B : matrix l p α}
  (i₁ i₂: l) (a b : α) (ha : a ≠ 0) (h : a + b ≠ 0 ∨ i₁ ≠ i₂): M ⬝ X = B ↔ (row_add_linear M i₁ i₂ a b) ⬝ X = (row_add_linear B i₁ i₂ a b) :=
begin
split,
{ exact testt _ _ _ _},
{ intro hh,
  by_cases h':i₁=i₂,
  {
    have hh':=testt i₁ i₂ (1/(a+b)) 0 hh,
    ext i j,
    have hh_i := ext_iff.2 hh' i j,
    simp [matrix.mul,row_add_linear_ite] at hh_i,
    cases h,
    { 
      by_cases h'':i=i₁,
      {
        simp [h',h'' ] at hh_i,
        simp [(right_distrib a b _).symm,(mul_assoc (a + b)⁻¹ _ _).symm,inv_mul_cancel h] at hh_i,
        rw [h'',h'], exact hh_i
      },
      simp [h',h'' ] at hh_i, exact hh_i
    },
    by_cases h'':i=i₁,
    {
      contradiction
    },
    simp [h',h''] at hh_i,
    exact hh_i
  }, 
  have hh':=testt i₁ i₂ (1/a) (-b/a) hh,
  ext i j,
  have hh_i := ext_iff.2 hh' i j,
  simp [matrix.mul,row_add_linear_ite] at hh_i,
  by_cases h'':i=i₁,
  {
    simp [ne_comm.1 h',h''] at hh_i,
    ring_nf at hh_i, simp [mul_assoc _ a _,mul_inv_cancel ha] at hh_i,
    rw [h''], exact hh_i
  },
  simp [ne_comm.1 h',h''] at hh_i,
  exact hh_i
}
end

def elementary_row_matrix [decidable_eq l] (i₁ i₂ : l) (a b : α) :  matrix l l α := 
  1 + b•(std_basis_matrix i₁ i₂ 1) + (a-1)•(std_basis_matrix i₁ i₁ 1)

lemma row_add_linear_eq_mul [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) (a b : α):
  row_add_linear M i₁ i₂ a b = (elementary_row_matrix i₁ i₂ a b) ⬝ M :=
begin
ext i j,
simp [elementary_row_matrix,row_add_linear_ite,mul_apply,std_basis_matrix,one_apply],
by_cases h:i = i₁,
{ 
  simp [h,@eq_comm _ i₁ _,add_comm,add_assoc,apply_ite2 has_add.add],
  simp [right_distrib,finset.sum_add_distrib]
},
simp [h]
end


def row_add_linear_seq [decidable_eq l] (M : matrix l o α) :
  list ((l × l) × (α × α)) → matrix l o α
| list.nil := M 
| (d::L') :=  row_add_linear (row_add_linear_seq L') d.1.1 d.1.2 d.2.1 d.2.2

lemma row_add_linear_seq_nil [decidable_eq l] (M : matrix l o α) :
  row_add_linear_seq M [] = M := rfl

lemma row_add_linear_seq_con 
  [decidable_eq l] (M : matrix l o α) (L : list ((l × l) × (α × α))) (d : (l × l) × (α × α)) :
  row_add_linear_seq M (d::L) = row_add_linear (row_add_linear_seq M L) d.1.1 d.1.2 d.2.1 d.2.2 := rfl

def good_list (L : list ((l × l) × (α × α))):= (∀ d : (l × l) × (α × α), d ∈ L → d.2.1 ≠ 0 ∧ (d.2.1 + d.2.2 ≠ 0 ∨ d.1.1 ≠ d.1.2)) 
@[simp]
lemma good_list_nil : good_list ([]:list ((l × l) × (α × α))) := by simp [good_list]

lemma good_list_append {L L' : list ((l × l) × (α × α))} : (good_list L ∧ good_list L') ↔ good_list (L++L') :=
⟨λ hL d hd,or.elim (list.mem_append.1 hd) (λ hdL,hL.1 d hdL) (λ hdL',hL.2 d hdL'),
λ H,⟨λ d hd,H _ (list.mem_append_left _ hd),λ d hd,H _ (list.mem_append_right _ hd)⟩⟩

lemma good_list_singleton {d : (l × l) × (α × α)} : 
  good_list [d] ↔ d.2.1 ≠ 0 ∧ (d.2.1 + d.2.2 ≠ 0 ∨ d.1.1 ≠ d.1.2) :=
begin
split,
{ intros h,
  exact h d (list.mem_singleton_self d)},
intros h d' hd',
simp [list.mem_singleton] at hd',simp [hd'],exact h
end

lemma good_list_con {d : (l × l) × (α × α)} (L : list ((l × l) × (α × α))) : 
  good_list (d :: L) ↔ good_list [d] ∧ good_list L := by simp [good_list_append]

lemma good_list_three (d₁ d₂ d₃ : (l × l) × (α × α)):
  good_list [d₁] → good_list [d₂] → good_list [d₃] → good_list [d₁,d₂,d₃] :=
by intros h₁ h₂ h₃;rw [←list.singleton_append,←@list.singleton_append _ d₂ _];
  exact good_list_append.1 ⟨h₁,good_list_append.1 ⟨h₂,h₃⟩⟩

lemma good_list_fn (f : fin n → ((l × l) × (α × α))): good_list (list.of_fn f) ↔ ∀ i:fin n, good_list [(f i)] :=
by unfold good_list;simp

lemma testt_seq_iff [decidable_eq l] {M : matrix l o α} {X : matrix o p α} {B : matrix l p α}
  (L : list ((l × l) × (α × α))) :
  good_list L
  → (M ⬝ X = B ↔ (row_add_linear_seq M L) ⬝ X = (row_add_linear_seq B L)) :=
begin
apply L.rec_on,
{ 
  simp [row_add_linear_seq]
},
intros d L' h' hh,
rw [row_add_linear_seq_con,row_add_linear_seq_con],
apply iff.trans (h' _),
exact testt_iff _ _ _ _ (hh d (list.mem_cons_self _ _)).1 (hh d (list.mem_cons_self _ _)).2,
intros d' hd',
exact hh d' (list.mem_cons_of_mem _ hd')
end

lemma row_add_linear_seq_eq_mul [decidable_eq l] (M : matrix l o α) (L : list ((l × l) × (α × α))):
  row_add_linear_seq M L = list.prod (L.map (λ d,elementary_row_matrix d.1.1 d.1.2 d.2.1 d.2.2)) ⬝ M :=
begin
induction L,
{
  simp [row_add_linear_seq]
},
rw [row_add_linear_seq_con],
simp [row_add_linear_eq_mul,L_ih],
exact ((elementary_row_matrix L_hd.fst.fst L_hd.fst.snd L_hd.snd.fst L_hd.snd.snd).mul_assoc
   (list.map (λ (d : (l × l) × α × α), elementary_row_matrix d.fst.fst d.fst.snd d.snd.fst d.snd.snd) L_tl).prod
   M).symm -- garbage from library_search 
end

lemma row_add_linear_seq_append [decidable_eq l] (M : matrix l o α) (L L': list ((l × l) × (α × α))) :
row_add_linear_seq M (L++L') = row_add_linear_seq (row_add_linear_seq M L') L :=
begin
induction L,
{simp [row_add_linear_seq_nil]},
{simp [list.cons_append,row_add_linear_seq_con,L_ih]}
end

def row_equiv [decidable_eq l] (M N: matrix l o α) : Prop := 
∃ L : list ((l × l) × (α × α)), 
  good_list L
  ∧ N = row_add_linear_seq M L

-- lemma row_equiv_iff_equiv [decidable_eq l] (M N: matrix l o α) :
--   row_equiv M N ↔ (∀ (X : matrix o p α) ,M ⬝ X = 0 ↔ N ⬝ X = 0) :=
-- begin

-- end

def swap_list [decidable_eq l] (i₁ i₂ : l) : list ((l × l) × (α × α)) :=
if i₁ = i₂ then [] else [⟨⟨i₁,i₂⟩,⟨1,-1⟩⟩,⟨⟨i₂,i₁⟩,⟨-1,1⟩⟩,⟨⟨i₁,i₂⟩,⟨1,1⟩⟩]
@[simp]
lemma swap_list_same [decidable_eq l] (i : l) :
swap_list i i = ([]:list ((l × l) × (α × α))) := by simp [swap_list]
@[simp]
lemma swap_list_neq [decidable_eq l] (i₁ i₂ : l) (h:i₁ ≠ i₂):
swap_list i₁ i₂ = ([⟨⟨i₁,i₂⟩,⟨1,-1⟩⟩,⟨⟨i₂,i₁⟩,⟨-1,1⟩⟩,⟨⟨i₁,i₂⟩,⟨1,1⟩⟩]:list ((l × l) × (α × α))) := 
by simp [swap_list,h]

lemma good_swap_list [decidable_eq l] (i₁ i₂ : l) :
  good_list (swap_list i₁ i₂ : list ((l × l) × (α × α))) :=
begin
intros d hd,
by_cases h:i₁ = i₂,
{ 
  exfalso,simp [h] at hd,exact hd
},
{
  rw [swap_list_neq _ _ h] at hd,
  refine good_list_three _ _ _ _ _ _ d hd;
  simp [good_list_singleton],exact h,exact ne.symm h,exact or.inr h
}
end

lemma swap_list_swaps_rows [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) :
  row_add_linear_seq M (swap_list i₁ i₂) = λ i j, if i=i₁ then M i₂ j else if i=i₂ then M i₁ j else M i j :=
begin
ext i j,
by_cases h:i₁=i₂,
{ simp [swap_list,h,row_add_linear_seq_nil],
  by_cases h':i=i₂;simp [h']},
{ simp [swap_list,h,row_add_linear_seq_con,row_add_linear,row_add_linear_seq_nil,update_row,function.update],
  by_cases h₁:i=i₁,
  { simp [h₁,ne.symm h]},
  simp [h₁],
  by_cases h₂:i=i₂,
  { simp [h₂,ne.symm h]},simp [h₂]}
end

lemma swap_swap_list [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l):
  row_add_linear_seq M (swap_list i₁ i₂ ++ swap_list i₂ i₁) = M := 
begin
  simp [row_add_linear_seq_append,swap_list_swaps_rows],
  ext, split_ifs;simp *
end

lemma swap_list_eq_symm [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) :
row_add_linear_seq M (swap_list i₁ i₂) = row_add_linear_seq M (swap_list i₂ i₁) :=
begin
  simp[swap_list_swaps_rows],
  ext,split_ifs,{rw [←h,←h_1]},{refl},{refl},{refl}
end

def nonnul_below [decidable_eq α] [linear_order l] (M : matrix l o α) (k : l): Prop := ∃ i≥k,∃ j, M i j ≠ 0

instance [decidable_eq α] [linear_order l] (M : matrix l o α) (k : l) : decidable (nonnul_below M k) :=
fintype.decidable_exists_fintype

lemma nonnul_below_not [decidable_eq α] [linear_order l] (M : matrix l o α) (k : l) :
  nonnul_below M k ↔ ¬ ∀ i≥k,∀ j,M i j = 0 :=
by simp [nonnul_below]

lemma nonnul_below_zero [decidable_eq α] (M : matrix (fin m.succ) o α) : nonnul_below M 0 ↔ M ≠ 0 :=
begin 
rw [nonnul_below_not,not_iff_not],split,
{ intros h,ext,exact h _ (fin.zero_le i) _},
intros hM i _ j,
exact ext_iff.2 hM _ _
end

def first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) : o :=
finset.min' (finset.filter (λ j,∃ i≥k, M i j ≠ 0) finset.univ) (let ⟨i,hi,j,hj⟩:=h in ⟨j,by simp;exact ⟨i,hi,hj⟩⟩)

lemma exists_nonnul_in_first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
  ∃ i≥k, M i (first_nonnul_col M k h) ≠ 0 :=
begin
have hh: (first_nonnul_col M k h) ∈ (finset.filter (λ j,∃ i≥k, M i j ≠ 0) finset.univ):=finset.min'_mem _ _,
simpa using hh,
end

def first_nonnul_in_first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k): l :=
finset.min' (finset.filter (λ i, i≥k ∧ M i (first_nonnul_col M k h) ≠ 0) finset.univ) (exists.elim (exists_nonnul_in_first_nonnul_col M k h) (λ i hi,⟨i,by simpa using hi⟩))

lemma first_nonnul_is_nonnul [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
first_nonnul_in_first_nonnul_col M k h ≥ k ∧ M (first_nonnul_in_first_nonnul_col M k h) (first_nonnul_col M k h) ≠ 0 :=
begin
have hh: (first_nonnul_in_first_nonnul_col M k h) ∈ (finset.filter (λ i, i≥k ∧ M i (first_nonnul_col M k h) ≠ 0) finset.univ):=finset.min'_mem _ _,
simpa using hh
end

def eliminating_list [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k:ℕ) (hk:k<m.succ) (h : nonnul_below M k): list ((fin m.succ × fin m.succ) × (α × α)) :=
  let i:=first_nonnul_in_first_nonnul_col M k h in
  let j:=first_nonnul_col M k h in
  (list.of_fn (λ i':fin k,⟨⟨i',⟨k,hk⟩⟩,⟨1,-M i' j⟩⟩)) ++ 
  swap_list k i ++ 
  (list.of_fn(λ i':fin (m-i),⟨⟨⟨nat.succ (i'+i),nat.succ_le_succ (nat.add_lt_of_lt_sub_right i'.property)⟩,i⟩,⟨1,-M ⟨nat.succ (i'+i),nat.succ_le_succ (nat.add_lt_of_lt_sub_right i'.property)⟩ j⟩⟩)) ++ 
  [⟨⟨i,i⟩,⟨1/M i j,0⟩⟩]



def eliminating_list_full [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) : ∀ k:ℕ, k<m.succ → ∀ (M' : matrix (fin m.succ) (fin n.succ) α), list ((fin m.succ × fin m.succ) × (α × α))
| 0 hk M':= if h : nonnul_below M' m then  eliminating_list M' m (lt_add_one m) h else []
| (nat.succ k) hk M' := let k':=m.succ-k.succ.succ in
  if h : nonnul_below M' k' then 
  eliminating_list_full k (nat.lt_of_succ_lt hk) 
    (row_add_linear_seq M' (eliminating_list M' k' (nat.sub_lt (nat.succ_pos _) (nat.succ_pos _)) h)) 
  ++ eliminating_list M' k' (nat.sub_lt (nat.succ_pos _) (nat.succ_pos _)) h else []

def gaussian [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) := 
row_add_linear_seq M (eliminating_list_full M m (lt_add_one m) M)

def matrix.to_list (M : matrix (fin m) (fin n) α) : list (list α) :=
list.of_fn (λ i:fin 
m,list.of_fn (λ j:fin n,M i j))


lemma good_eliminating_list [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k:ℕ) (hk:k<m.succ) (h : nonnul_below M k) :
good_list (eliminating_list M k hk h) :=
begin
unfold eliminating_list,
refine good_list_append.1 ⟨good_list_append.1 ⟨good_list_append.1  ⟨_,_⟩,_⟩,_⟩,
{ simp [good_list_fn],intro i',simp [good_list_singleton],
  apply or.inr,simp [fin.eq_iff_veq],unfold_coes,apply ne_of_lt,
  rw [nat.mod_eq_of_lt (lt_trans i'.property hk)],exact i'.property
},
{ exact good_swap_list _ _},
{ simp [good_list_fn], intro i',
  simp [good_list_singleton],
  apply or.inr,simp [fin.eq_iff_veq],
  rw [nat.succ_eq_add_one],linarith},
{ simp [good_list_singleton];exact (first_nonnul_is_nonnul M k h).2}
end

lemma good_list_gaussian [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) :
∀ (k:ℕ) (hk:k<m.succ) (M' : matrix (fin m.succ) (fin n.succ) α), 
good_list (eliminating_list_full M k hk M') :=
begin
intro k,
induction k with k' h,
{ intros hk M',unfold eliminating_list_full,split_ifs,
  { exact good_eliminating_list _ _ _ _},
  exact good_list_nil},
intros hk M',simp [eliminating_list_full],split_ifs,
{ refine good_list_append.1 ⟨_,_⟩,
  { exact h _ _},
    exact good_eliminating_list _ _ _ _},
exact good_list_nil
end --POOOOOOOOG





def M := ![![(1:ℚ),0,2,3],![2,0,4,6],![0,2,2,0],![1,2,4,3]]
def M' : matrix (fin 3) (fin 3) ℚ  := ![![0,0,0],![0,0,0],![0,5,6]]



#eval matrix.to_list $ gaussian M






-- def row_equivalent (M N : matrix m n α) : Prop :=
-- ∃ 




def leading_entry (M : matrix (fin m) (fin n) α) (i : fin m) (j : fin n) :=
  ∀ j',j'<j→ M i j'=0

lemma eliminating_leading_entry [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k : ℕ) (hk : k<m.succ) (h : nonnul_below M k): 
leading_entry (row_add_linear_seq M (eliminating_list M k hk h)) (first_nonnul_in_first_nonnul_col M k h) (first_nonnul_col M k h) :=
begin
intros j' hj,
simp [eliminating_list,row_add_linear_seq_append],
end

def row_echelon_form (M : matrix (fin m) (fin n) α) : Prop := 
(∀ i i', (∀ j, M i j ≠ 0) → (∀ j, M i' j = 0) → i' < i)
∧ (∀ i i' j j', i < i' → leading_entry M i j → leading_entry M i' j' → j <j')




-- def upper_triangle (M : matrix m m α) : Prop :=
-- ∀ i j, j < i → M i j = 0

-- lemma eirhih (M : matrix m m α) : row_echelon_form M ↔ upper_triangle M :=
-- ⟨λ h i j hij,_,_⟩