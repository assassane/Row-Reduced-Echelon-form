/-
Author : Anas Himmi

The goal of this file is to implement elementary row operations, elmentary row matrices, row equivalence,
  gaussian elimination, and row reduced echelon form, and prove basic theorems about them.


important definitions in this file:

  row_add_linear : applies an elementary row operation
    here instead of considering the 3 usual row operations (switching, multiplication and addition), 
    we aggregate them into a single row operation Rᵢ <- a*Rᵢ+b*Rⱼ
  row_add_linear_seq : applies a finite sequence of elementary row operations using a list (from left to right)
  elementary_row_matrix : the matrix corresponding to an elementary row operation
  good_list (should be renamed) : the sequence of operations doesn't change the range of the matrix
  row_equiv : two matrices are row equivalent if we can obtain one from a sequence of elementary row operations
    on the other
    --TODO : show it is an equivalence relation
  swap_list : a list of elementary row operations corresponding to switching two rows
  nonnul_below : there is a nonnul element below the k_th row
  first_nonnul_col : the first (most left) nonnul column of a matrix if we consider the rows below the k_th row
  first_nonnul_in_first_nonnul_col : the first (most up) nonnul element in the first_nonnul_col below the k_th row
  eliminating_list : list of elementary row operations corresponding to one step of gaussian elimination
  gaussian_elimination : give the row reduced echelon form of he matrix using gaussian elimination
  gaussian_elimination_list : gives the list of elementary row operations necessary to obtain RREF matrix
  gaussian_elimination_rank : gives the rank of the matrix using gaussian elimination (not yet proven)
  leading_entry : first (most left) nonnul element of row
  RREF : a matrix is in row reduced echelon form
  first_nul_row : first (most up) nul row



  WORK IN PROGRESS
-/



import linear_algebra.determinant tactic.ring tactic.linarith data.matrix.pequiv data.matrix.notation
import tactic.unfold_cases tactic.field_simp
import algebra.order.sub
universes u u' v w
variables {m n : ℕ} {l o p: Type*} [fintype l] [fintype o] [fintype p]
variables {α : Type v} [field α]

open matrix

localized "infixl ` ⬝ `:75 := matrix.mul" in matrix


-- Rᵢ₁ ← a*Rᵢ₁+b*Rᵢ₂ 
def row_add_linear [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) (a b : α) :
  matrix l o α :=
update_row M i₁ (λ c,a • M i₁ c + b • M i₂ c)


lemma row_add_linear_ite [decidable_eq l] (M : matrix l o α) (i₁ i₂ : l) (a b : α): 
  row_add_linear M i₁ i₂ a b = (λ i j,if i = i₁  then a * M i₁ j + b * M i₂ j else M i j) := 
by ext i j;simp [row_add_linear];by_cases h_:i = i₁;simp [h_]

lemma row_add_linear_zero [decidable_eq l] (i₁ i₂ : l) (a b : α) :
  row_add_linear (0:matrix l o α) i₁ i₂ a b = 0 :=
  by ext i j;simp [row_add_linear_ite]

lemma linear_system_stable_row_add_linear [decidable_eq l] {M : matrix l o α} {X : matrix o p α} {B : matrix l p α}
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
  rw [←h_i₁,←h_i₂,←smul_eq_mul,←smul_eq_mul,←smul_dot_product,←smul_dot_product,←add_dot_product],
  have h_h:(λ j_1, a * M i₁ j_1 + b * M i₂ j_1) = a • M i₁ + b • M i₂,from rfl,
  rw [h_h]
},
exact ext_iff.2 h i j
end


lemma linear_system_stable_row_add_linear_iff [decidable_eq l] {M : matrix l o α} {X : matrix o p α} {B : matrix l p α}
  (i₁ i₂: l) (a b : α) (ha : a ≠ 0) (h : a + b ≠ 0 ∨ i₁ ≠ i₂): M ⬝ X = B ↔ (row_add_linear M i₁ i₂ a b) ⬝ X = (row_add_linear B i₁ i₂ a b) :=
begin
split,
{ exact linear_system_stable_row_add_linear _ _ _ _},
{ intro hh,
  by_cases h':i₁=i₂,
  {
    have hh':=linear_system_stable_row_add_linear i₁ i₂ (1/(a+b)) 0 hh,
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
      simp [←h',h'' ] at hh_i,exact hh_i
    },
    by_cases h'':i=i₁,
    {
      contradiction
    },
    simp [←h',h''] at hh_i,
    exact hh_i
  }, 
  have hh':=linear_system_stable_row_add_linear i₁ i₂ (1/a) (-b/a) hh,
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
by_cases h:i = i₁,{
  simp [h,@eq_comm _ i₁ _,add_comm,add_assoc,apply_ite2 has_add.add],
  simp [right_distrib,finset.sum_add_distrib,add_comm]},
simp [h,@eq_comm _ i₁ _]
end


def row_add_linear_seq [decidable_eq l] (M : matrix l o α) :
  list ((l × l) × (α × α)) → matrix l o α
| list.nil := M 
| (d::L') :=  row_add_linear (row_add_linear_seq L') d.1.1 d.1.2 d.2.1 d.2.2

lemma row_add_linear_seq_zero [decidable_eq l] (L : list ((l × l) × (α × α))) :
  row_add_linear_seq (0:matrix l o α) L = 0 :=
begin induction L,{refl},unfold row_add_linear_seq,rw [L_ih,row_add_linear_zero] end

lemma row_add_linear_seq_nil [decidable_eq l] (M : matrix l o α) :
  row_add_linear_seq M [] = M := rfl

lemma row_add_linear_seq_con 
  [decidable_eq l] (M : matrix l o α) (L : list ((l × l) × (α × α))) (d : (l × l) × (α × α)) :
  row_add_linear_seq M (d::L) = row_add_linear (row_add_linear_seq M L) d.1.1 d.1.2 d.2.1 d.2.2 := rfl

@[simp]
lemma row_add_linear_seq_singleton [decidable_eq l] (M : matrix l o α) (d : (l × l) × (α × α)) :
  row_add_linear_seq M [d] = row_add_linear M d.1.1 d.1.2 d.2.1 d.2.2 :=
by tidy


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

lemma linear_system_stable_row_add_linear_seq_iff [decidable_eq l] {M : matrix l o α} {X : matrix o p α} {B : matrix l p α}
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
exact linear_system_stable_row_add_linear_iff _ _ _ _ (hh d (list.mem_cons_self _ _)).1 (hh d (list.mem_cons_self _ _)).2,
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

lemma row_add_linear_nul_col [decidable_eq l] (M : matrix l o α) (j:o) (h:∀ i,M i j = 0) (d : (l × l) × (α × α)) :
∀ i,row_add_linear M d.1.1 d.1.2 d.2.1 d.2.2 i j = 0 :=
λ i,by simp [row_add_linear_ite];split_ifs;simp [h d.1.1, h d.1.2, h i]


lemma row_add_linear_seq_nul_col [decidable_eq l] (L:list ((l × l) × (α × α))) :
∀ (M : matrix l o α) (j:o) (h:∀ i,M i j = 0) i,row_add_linear_seq M L i j = 0 :=
list.rec_on L (by intros; rw [row_add_linear_seq_nil];exact h i) 
(λ d L hL M j h i,by rw [row_add_linear_seq_con];exact row_add_linear_nul_col _ _ (hL _ _ h) _ _)


lemma row_add_linear_seq_eq_row [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) 
  (L : list ((fin m.succ × fin m.succ) × (α × α)))
  (i : fin m.succ)
  (hL : ∀ d:(fin m.succ × fin m.succ) × (α × α),d∈L → d.1.1 = i → d.2.1 = 1 ∧ d.2.2 = 0):
  ∀ j,row_add_linear_seq M L i j = M i j :=
begin
intro j,
induction L with d L hL',
{ rw [row_add_linear_seq_nil]},
{ simp [row_add_linear_seq_con,row_add_linear_ite],split_ifs,
  { simp [hL d (list.mem_cons_self _ L) h.symm,←h],
  apply hL',intros d' hd',exact hL d' (list.mem_cons_of_mem _ hd')},
  apply hL',intros d' hd',exact hL d' (list.mem_cons_of_mem _ hd')}
end


lemma bot_left_of_nul_block [decidable_eq α] (M : matrix (fin m.succ) (fin n) α)
  (i':fin m.succ) (j':fin n.succ) 
  (hM : ∀ i (j:fin j'.val),i' ≤ i → M i (fin.cast_le (nat.le_of_lt_succ j'.property) j) = 0)
  (L : list ((fin m.succ × fin m.succ) × (α × α)))
  (hL : ∀ d:(fin m.succ × fin m.succ) × (α × α), d∈ L → i' ≤ d.1.1 → i' ≤ d.1.2) :
    ∀ i (j:fin n),i' ≤ i → j.cast_succ < j' →  row_add_linear_seq M L i j = 0 :=
begin
induction L with d L hL',
{ intros i j hi hj,rw [row_add_linear_seq_nil],have := hM i ⟨j,hj⟩ hi,simp at this,exact this},
{ intros i j hi hj,
  have := hL d (list.mem_cons_self _ _),
  simp [row_add_linear_seq_con,row_add_linear_ite],
  split_ifs,
  { rw ←h at this,replace this := this hi, rw h at hi,
    simp [hL' (λ d' hd',hL d' (list.mem_cons_of_mem d hd')) _ _ this hj,
    hL' (λ d' hd',hL d' (list.mem_cons_of_mem d hd')) _ _ hi hj]},
  { exact hL' (λ d' hd' hd'',hL _ (list.mem_cons_of_mem d hd') hd'') _ _ hi hj}}
end

--could be more general using fintype.choose but would be useless for this file
lemma row_add_linear_seq_of_fn [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k: ℕ) : 
∀ (c: ℕ) (hkc : k + c ≤ m.succ) (g : fin k → fin m.succ) 
(hg : ∀ i, (g i).val  < c ∨ (g i).val ≥ c + k ∨ g i = ⟨i.val + c,lt_of_lt_of_le (nat.add_lt_add_right i.property _) hkc⟩) 
(a₁ a₂ : fin k → α),
  row_add_linear_seq M (list.of_fn (λ i:fin k, ⟨⟨⟨i.val+c,lt_of_lt_of_le (nat.add_lt_add_right i.property _) hkc⟩,g i⟩,⟨a₁ i,a₂ i⟩⟩)) = 
  λ i j, if h : c ≤ i.val ∧ i.val - c < k then a₁ ⟨i.val - c,h.2⟩ * M i j + a₂ ⟨i.val - c,h.2⟩ * M (g ⟨i.val - c,h.2⟩) j  else M i j :=
begin
induction k with k' hk',
{ intros,
  ext i j,
  split_ifs with hf hf,
  { exfalso,exact nat.not_lt_zero _ hf.2},
  simp [row_add_linear_seq_nil]},
intros,
simp [row_add_linear_seq_con],
have := hk' c.succ (by rwa [nat.succ_add] at hkc) (λ x, g x.succ) _ (λ x, a₁ x.succ) (λ x, a₂ x.succ),
have h_ : ¬(c.succ ≤ c ∧ c - c.succ < k'),by simp [nat.not_succ_le_self],
ext i j,
simp at this, simp [add_assoc _ 1 c,nat.one_add c,this,row_add_linear_ite,h_],
split_ifs,
{ exfalso,
  cases (hg 0) with ho ho',
  { exact not_le_of_lt ho (nat.le_of_succ_le h_1.1)},cases ho' with ho ho,
  { apply not_lt_of_le ho,
    simp [tsub_lt_iff_left h_1.1,nat.succ_add_eq_succ_add] at h_1,
    exact h_1.2},
  { simp [ho] at h_1,
    exact nat.not_succ_le_self _ h_1.1}
},
{ exfalso,
  cases (hg 0) with ho ho',
  { exact not_le_of_lt ho (nat.le_of_succ_le h_1.1)},cases ho' with ho ho,
  { apply not_lt_of_le ho,
    simp [tsub_lt_iff_left h_1.1,nat.succ_add_eq_succ_add] at h_1,
    exact h_1.2},
  { simp [ho] at h_1,
    exact nat.not_succ_le_self _ h_1.1}
},
{simp [h]},
{exfalso, simp [h] at h_2,exact h_2},
{ have : ↑i - c > 0,from nat.lt_of_le_and_ne (zero_le (i.val - c)) (λ hn,absurd (le_antisymm (nat.sub_eq_zero_iff_le.1 hn.symm) h_2.1) ((not_iff_not.2 (fin.eq_iff_veq _ _)).1 h)),
  simp [fin.succ,nat.sub_succ,←nat.succ_eq_add_one,nat.succ_pred_eq_of_pos this],},
{simp at h_2, exfalso,
apply not_lt_of_le (h_2 (le_of_lt h_1.1)),
apply nat.lt_succ_iff.2, rw [nat.sub_succ,nat.lt_iff_add_one_le,nat.add_one] at h_1,
have : ↑i - c > 0,from nat.sub_pos_of_lt h_1.1,
rw [nat.succ_pred_eq_of_pos this] at h_1, exact h_1.2},
{exfalso,simp at h_1,
have := h_1 (nat.lt_of_le_and_ne h_2.1 (ne_comm.1 ((not_iff_not.2 (fin.eq_iff_veq _ _)).1 h))),
apply not_lt_of_le this, rw [nat.sub_succ],
exact nat.pred_lt_pred (λ hn,absurd (le_antisymm (nat.sub_eq_zero_iff_le.1 hn) h_2.1) ((not_iff_not.2 (fin.eq_iff_veq _ _)).1 h)) (h_2.2) },
{simp},

{intro i, cases (hg i.succ) with ho ho',
  { apply or.inl,exact nat.lt.step ho},{ cases ho' with ho ho,
  { apply or.inr, apply or.inl, rw [nat.succ_add],exact ho},
  { apply or.inr, apply or.inr, simp [fin.succ, nat.succ_add] at ho,exact ho}}
}

end

def row_equiv [decidable_eq l] (M N: matrix l o α) : Prop := 
∃ L : list ((l × l) × (α × α)), 
  good_list L
  ∧ N = row_add_linear_seq M L

lemma row_equiv_iff_equiv [decidable_eq l] (M N: matrix l o α) :
  row_equiv M N ↔ (∀ (X : matrix o p α) ,M ⬝ X = 0 ↔ N ⬝ X = 0) :=
sorry --TODO



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

lemma nonnul_below_iff_not_forall [decidable_eq α] [linear_order l] (M : matrix l o α) (k : l) :
  nonnul_below M k ↔ ¬ ∀ i≥k,∀ j,M i j = 0 :=
by simp [nonnul_below]

lemma nonnul_below_zero [decidable_eq α] (M : matrix (fin m.succ) o α) : nonnul_below M 0 ↔ M ≠ 0 :=
begin 
rw [nonnul_below_iff_not_forall,not_iff_not],split,
{ intros h,ext,exact h _ (fin.zero_le i) _},
intros hM i _ j,
exact ext_iff.2 hM _ _
end

lemma not_nonnul_below_iff_forall [decidable_eq α] [linear_order l] (M : matrix l o α) (k : l) :
  (¬ nonnul_below M k) ↔ ∀ i≥k,∀ j,M i j = 0 := (iff_not_comm.1 (nonnul_below_iff_not_forall M k)).symm

def first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) : o :=
finset.min' (finset.filter (λ j,∃ i,k≤i ∧ M i j ≠ 0) finset.univ) (let ⟨i,hi,j,hj⟩:=h in ⟨j,by simp;exact ⟨i,hi,hj⟩⟩)

lemma exists_nonnul_in_first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
  ∃ i≥k, M i (first_nonnul_col M k h) ≠ 0 :=
begin
have hh: (first_nonnul_col M k h) ∈ (finset.filter (λ j,∃ i,k≤i ∧ M i j ≠ 0) finset.univ):=finset.min'_mem _ _,
simpa using hh,
end

lemma first_nonnul_col_le [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
∀ j,(∃ i,k≤i ∧ M i j ≠ 0) → first_nonnul_col M k h ≤ j :=
λ j hj,finset.min'_le _ _ (finset.mem_filter.2 ⟨finset.mem_univ _,hj⟩)

lemma lt_first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
∀ j,(∀ j',j'≤j→ ∀ i,k ≤ i → M i j' = 0) → j < first_nonnul_col M k h :=
λ j hj,lt_of_le_of_ne (finset.le_min' _ _ _ (λ y hy,by {apply le_of_not_le,intro hyy,simp at hy,rcases hy with ⟨i,hi⟩,apply hi.2,apply hj,assumption,exact hi.1}))
(λ hn,let ⟨i,hik,hi⟩:=exists_nonnul_in_first_nonnul_col M k h in hi $ hj _ (eq.ge hn) _ hik)

lemma fisrt_nonnul_col_is_first [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
  ∀ i j, k ≤ i → j < first_nonnul_col M k h → M i j = 0 :=
λ i j hi hj,or.elim (decidable.em (M i j = 0)) id 
  (λ ho,false.elim $ not_le_of_lt hj (first_nonnul_col_le _ _ _ _ ⟨i,hi,ho⟩))

lemma first_nonnul_col_is_unique [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
∀ j, (∃ i,k≤i ∧ M i j ≠ 0) → (∀ j', (∃ i,k≤i ∧ M i j' ≠ 0) → j ≤ j') → j = first_nonnul_col M k h :=
λ j hj hj',
le_antisymm (finset.le_min' _ _ _ (λ y hy,by simp at hy;exact hj' y hy)) (finset.min'_le _ _ (by simp;exact hj))

lemma first_nonnul_col_last [decidable_eq α] [linear_order o] (M : matrix (fin m.succ) o α) (h : nonnul_below M (fin.last m)) :
M (fin.last m) (first_nonnul_col M _ h) ≠ 0 :=
begin
obtain ⟨i,hi,hh⟩:= exists_nonnul_in_first_nonnul_col M _ h,
have : i = fin.last m,from le_antisymm (nat.le_of_lt_succ i.property) hi,
rwa this at hh
end

def first_nonnul_in_first_nonnul_col [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k): l :=
finset.min' (finset.filter (λ i, k≤i ∧ M i (first_nonnul_col M k h) ≠ 0) finset.univ) 
(let ⟨i,hi⟩:=exists_nonnul_in_first_nonnul_col M k h in ⟨i,by simpa using hi⟩)


lemma first_nonnul_is_nonnul [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
k ≤ first_nonnul_in_first_nonnul_col M k h ∧ M (first_nonnul_in_first_nonnul_col M k h) (first_nonnul_col M k h) ≠ 0 :=
begin
have hh: (first_nonnul_in_first_nonnul_col M k h) ∈ (finset.filter (λ i, k≤i ∧ M i (first_nonnul_col M k h) ≠ 0) finset.univ):=finset.min'_mem _ _,
simpa using hh
end

lemma first_nonnul_is_first [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) (i : l):
i < first_nonnul_in_first_nonnul_col M k h →  k ≤ i →  M i (first_nonnul_col M k h) = 0 :=
λ h₁ h₂,or.elim (decidable.em (M i (first_nonnul_col M k h) = 0)) id 
  (λ ho,false.elim $ not_le_of_lt h₁ (finset.min'_le _ i (finset.mem_filter.2 ⟨finset.mem_univ i,h₂,ho⟩)))

lemma first_nonnul_le [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
∀ i,k ≤ i → M i (first_nonnul_col M k h) ≠ 0 → first_nonnul_in_first_nonnul_col M k h ≤ i :=
λ i hki hi,finset.min'_le _ _ (finset.mem_filter.2 ⟨finset.mem_univ _,hki,hi⟩)

lemma first_nonnul_is_unique [decidable_eq α] [linear_order l] [linear_order o] (M : matrix l o α) (k : l) (h : nonnul_below M k) :
∀ i,k ≤ i → M i (first_nonnul_col M k h) ≠ 0 → (∀ i',k ≤ i → M i (first_nonnul_col M k h) ≠ 0 → i ≤ i') → i = first_nonnul_in_first_nonnul_col M k h :=
λ i hki hi hi',
le_antisymm (finset.le_min' _ _ _ (λ y hy,by simp at hy;exact hi' y hki hi)) (finset.min'_le _ _ (by simp;exact ⟨hki,hi⟩))


def eliminating_list [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k:fin m.succ) (h : nonnul_below M k): list ((fin m.succ × fin m.succ) × (α × α)) :=
  let i:=first_nonnul_in_first_nonnul_col M k h in
  let j:=first_nonnul_col M k h in
  (list.of_fn (λ i':fin k.val,⟨⟨⟨i'.val,lt_trans i'.property k.property⟩,k⟩,⟨1,-M ⟨i'.val,lt_trans i'.property k.property⟩ j⟩⟩)) ++ 
  swap_list k i ++ 
  (list.of_fn(λ i':fin (m-i.val),⟨⟨⟨i'.val+i.val.succ,lt_tsub_iff_right.1 ((nat.succ_sub_succ m i.val).symm ▸ i'.property)⟩,i⟩,⟨1,-M ⟨i'.val+i.val.succ,lt_tsub_iff_right.1 ((nat.succ_sub_succ m i.val).symm ▸ i'.property)⟩ j⟩⟩)) ++ 
  [⟨⟨i,i⟩,⟨1/M i j,0⟩⟩]


def gaussian_elimination_aux [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α):∀ k':ℕ, k'<m.succ.succ → (matrix (fin m.succ) (fin n.succ) α) × list ((fin m.succ × fin m.succ) × (α × α)) × ℕ
| 0 hk' := ⟨M,[],0⟩
| (nat.succ k') hk' := let M'L := (gaussian_elimination_aux k' (nat.lt_of_succ_lt hk')) in 
  if h : nonnul_below M'L.1 ⟨k',nat.succ_lt_succ_iff.mp hk'⟩  then 
    let L := (eliminating_list M'L.1 ⟨k',nat.succ_lt_succ_iff.mp hk'⟩ h) in
  ⟨row_add_linear_seq M'L.1 L ,L ++ M'L.2.1,M'L.2.2.succ⟩
  else M'L


def gaussian_elimination_all [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) : (matrix (fin m.succ) (fin n.succ) α) × list ((fin m.succ × fin m.succ) × (α × α)) × ℕ :=
gaussian_elimination_aux M (min n.succ m.succ) (min_lt_iff.2 (or.inr (lt_add_one (nat.succ m))))

def gaussian_elimination [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) :=
(gaussian_elimination_all M).1

def gaussian_elimination_list [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) :=
(gaussian_elimination_all M).2.1

def gaussian_elimination_rank [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) := 
(gaussian_elimination_all M).2.2

def matrix.to_list (M : matrix (fin m) (fin n) α) : list (list α) :=
list.of_fn (λ i:fin m,list.of_fn (λ j:fin n,M i j))


lemma good_eliminating_list [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k : fin m.succ) (h : nonnul_below M k) :
good_list (eliminating_list M k h) :=
begin
unfold eliminating_list,
refine good_list_append.1 ⟨good_list_append.1 ⟨good_list_append.1  ⟨_,_⟩,_⟩,_⟩,
{ simp [good_list_fn],intro i',simp [good_list_singleton],
  apply or.inr,apply ne_of_lt,
  exact i'.property
},
{ exact good_swap_list _ _},
{ simp [good_list_fn], intro i',
  simp [good_list_singleton],
  apply or.inr,simp [fin.eq_iff_veq],
  simp [nat.succ_eq_add_one],linarith},
{ simp [good_list_singleton];exact (first_nonnul_is_nonnul M k h).2}
end

lemma good_list_gaussian [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k' : ℕ) (hk' : k' < m.succ.succ):
good_list (gaussian_elimination_aux M k' hk').2.1 :=
begin
induction k' with k' hkk',
{ simp [gaussian_elimination_aux]},
{ simp [gaussian_elimination_aux],
  split_ifs,
  { apply good_list_append.1 ⟨_,_⟩,
    { apply good_eliminating_list},
    { apply hkk'}},
  { apply hkk'}}
end


lemma sub_left_eq {m n p : ℕ} (M : matrix (fin m) (fin (n+p)) α) {i : fin m} {j : fin (n+p)}
(h : j.val < n) : M.sub_left i (j.cast_lt h) = M i j :=
by unfold sub_left;simp

lemma sub_left_eq' {m n p : ℕ} (M : matrix (fin m) (fin (n+p)) α) {i : fin m} {j : fin n}
 : M.sub_left i j = M i (fin.cast_add _ j) := by unfold sub_left;simp

lemma sub_left_add_zero (M : matrix (fin m) (fin (n+0)) α) :
M.sub_left = M := by unfold sub_left;simp

lemma sub_up_eq {m n p : ℕ} (M : matrix (fin (m+p)) (fin n) α) {i : fin (m+p)} {j : fin n}
(h : i.val < m) : M.sub_up (i.cast_lt h) j = M i j :=
by unfold sub_up;simp

lemma sub_up_eq' {m n p : ℕ} (M : matrix (fin (m+p)) (fin n) α) {i : fin m} {j : fin n}
 : M.sub_up i j = M (fin.cast_add _ i) j := by unfold sub_up;simp

lemma sub_up_add_zero (M : matrix (fin (m+0)) (fin n) α) :
M.sub_up = M := by unfold sub_up;simp

def leading_entry [decidable_eq α] (M : matrix (fin m) (fin n) α) (i : fin m) (h:∃ j,M i j ≠ 0)  : fin n :=
finset.min' (finset.filter (λ j,M i j ≠ 0) finset.univ) (let ⟨j,hj⟩:= h in ⟨j,by simpa using hj⟩)

lemma leading_entry_nonnul [decidable_eq α] (M : matrix (fin m) (fin n) α) (i : fin m) (h:∃ j,M i j ≠ 0) :
  M i (leading_entry M i h) ≠ 0:=
begin
have hh: (leading_entry M i h) ∈ (finset.filter (λ j,M i j ≠ 0) finset.univ):=finset.min'_mem _ _,
simpa using hh,
end

lemma le_leading_entry [decidable_eq α] (M : matrix (fin m) (fin n) α) (i : fin m) (h:∃ j,M i j ≠ 0) :
∀ j:fin n, (∀ j', M i j' ≠ 0 → j ≤ j') → j ≤ leading_entry M i h :=
λ j hj,finset.le_min' _ _ _ (λ j' hj',hj _ (by simpa using hj'))

lemma leading_entry_is_leading [decidable_eq α] (M : matrix (fin m) (fin n) α) (i : fin m) (h:∃ j,M i j ≠ 0) :
  ∀ j,M i j ≠ 0 → leading_entry M i h ≤ j :=
λ j hj,finset.min'_le _ _ (by simpa using hj)

lemma leading_entry_unique [decidable_eq α] (M : matrix (fin m) (fin n) α) (i : fin m) (h:∃ j,M i j ≠ 0) (j : fin n):
  (M i j ≠ 0) → (∀ j',M i j' ≠ 0 → j ≤ j') → j = leading_entry M i h :=
λ hj hj', le_antisymm (finset.le_min' _ _ _ (λ y hy,hj' _ (by simpa using hy))) (leading_entry_is_leading _ _ _ _ hj)

lemma nul_of_lt_leading_entry [decidable_eq α] (M : matrix (fin m) (fin n) α) (i : fin m) (h:∃ j,M i j ≠ 0) (j : fin n) :
 j < leading_entry M i h → M i j = 0 :=
begin
intro hj,
have hh:= decidable.not_imp_not.2 (leading_entry_is_leading M i h j),
simp at hh,
exact hh hj
end

lemma leading_entry_succ_eq_leading_entry [decidable_eq α] (M : matrix (fin m) (fin n.succ) α) (i : fin m) (h : ∃ j:fin n,M i ⟨j.val,_⟩ ≠ 0):
  leading_entry M i (exists.elim h (λ j hj,⟨⟨j.val,nat.lt.step j.property⟩,hj⟩)) = 
⟨(leading_entry (λ (i:fin m) (j:fin n),M i ⟨j.val,nat.lt.step j.property⟩) i h).val,nat.lt.step (leading_entry (λ (i : fin m) (j : fin n), M i ⟨j.val, nat.lt.step j.property⟩) i h).property⟩ :=
(leading_entry_unique _ _ _ _ (by have := leading_entry_nonnul (λ (i:fin m) (j:fin n),M i ⟨j.val,nat.lt.step j.property⟩) i h;simp at this;exact this) 
(λ j' hj',or.elim (lt_or_eq_of_le (nat.le_of_lt_succ j'.property)) 
(λ ho,by have:=leading_entry_is_leading (λ (i:fin m) (j:fin n),M i ⟨j.val,nat.lt.step j.property⟩) i h ⟨j'.val,ho⟩ (by simp;exact hj');
  simp at this;exact this) 
(λ ho,by rw [(@fin.eq_mk_iff_coe_eq _ _ _ (lt_add_one n)).2 ho];exact le_of_lt ((leading_entry (λ (i : fin m) (j : fin n), M i ⟨↑j, _⟩) i _).property) ))).symm

lemma leading_entry_eq_sub_left [decidable_eq α] (q : ℕ) (M : matrix (fin m) (fin (n + q)) α) (i : fin m) (h : ∃ j:fin n, M i (fin.cast_add _ j) ≠ 0) :
leading_entry M i (exists.elim h (λ j hj,⟨fin.cast_add _ j,hj⟩)) = fin.cast_add _ (leading_entry M.sub_left i h) :=
begin
apply eq.symm, apply leading_entry_unique,
rw [←sub_left_eq' M], apply leading_entry_nonnul,
intros j' hj', rw [fin.le_iff_coe_le_coe,fin.coe_cast_add],
cases lt_or_le ↑j' n with hjn hjn,
{ have hh:= leading_entry_is_leading M.sub_left i h (fin.cast_lt j' hjn),
  rw [sub_left_eq] at hh, exact hh hj'},
exact le_trans (le_of_lt (leading_entry M.sub_left i h).property) hjn
end

lemma first_nonnul_col_eq_leading_entry [decidable_eq α] (M : matrix (fin m) (fin n) α) (k : fin m) (h : nonnul_below M k): 
  first_nonnul_col M k h = leading_entry M (first_nonnul_in_first_nonnul_col M k h) ⟨_,(first_nonnul_is_nonnul _ _ _).2⟩ :=
leading_entry_unique _ _ _ _ (first_nonnul_is_nonnul _ _ _).2 (λ j' hj',first_nonnul_col_le _ _ _ _ ⟨_,(first_nonnul_is_nonnul _ _ _).1,hj'⟩)

def RREF [decidable_eq α] (M : matrix (fin m) (fin n) α) : Prop := 
  (∀ i,(∀ j,M i j = 0) → ∀ i', i < i' → ∀ j,M i' j = 0) --nul rows are at the bottom
∧ (∀ i (hi:∃ j,M i j ≠ 0) i' (hii' : i < i') (hi':∃ j,M i' j ≠ 0),
    leading_entry M i hi < leading_entry M i' hi') -- leading entries are in order
∧ (∀ i (hi:∃ j,M i j ≠ 0), M i (leading_entry M i hi) = 1) -- leading entries are equal to one
∧ (∀ i (hi:∃ j,M i j ≠ 0) i' (hii':i ≠ i'), M i' (leading_entry M i hi) = 0  ) -- leading entries are only nonnul in col

instance [decidable_eq α] (M : matrix (fin m) (fin n) α) : decidable (RREF M) := 
and.decidable


lemma RREF_no_col [decidable_eq α] (M : matrix (fin m) (fin 0) α) : RREF M :=
⟨λ i hi i' hii' j,false.elim (j.val.not_lt_zero j.property),
λ i hi,let ⟨j,_⟩:= hi in false.elim (j.val.not_lt_zero j.property),
λ i hi,let ⟨j,_⟩:= hi in false.elim (j.val.not_lt_zero j.property),
λ i hi,let ⟨j,_⟩:= hi in false.elim (j.val.not_lt_zero j.property)⟩



lemma RREF_of_RREF_succ [decidable_eq α] (M : matrix (fin m) (fin (n+1)) α) (hM : RREF M) :
  RREF (matrix.sub_left M) :=
⟨λ i hi i' hii' j,or.elim (decidable.em (M i (fin.last _) = 0)) 
  (λ ho,hM.1 i (λ j',or.elim (eq_or_lt_of_le (fin.le_last j')) 
    (λ ho',by simpa [←ho'] using ho) 
    (λ ho',by simpa [sub_left_eq] using hi (fin.cast_lt j' ho'))) _ hii' _) 
  (λ ho,
    begin
    have hle:=leading_entry_unique M i ⟨⟨n,lt_add_one n⟩,ho⟩ ⟨n,_⟩ ho _,
    simp [sub_left_eq'],
    { cases (decidable.em (M i' (fin.cast_succ j) = 0)) with hn hn,
      { exact hn},
      { exfalso,
        have hi':∃ (j : fin n.succ), M i' j ≠ 0:=⟨(fin.cast_succ j),hn⟩,
        have hnle:=hM.2.1 i ⟨fin.last n,ho⟩ i' hii' hi',
        rw [hle.symm,fin.coe_fin_lt.symm,fin.coe_eq_val,fin.mk_val] at hnle,
        have hlen: (leading_entry M i' hi').val < n.succ := (leading_entry M i' hi').property,
        apply not_le_of_lt hnle,
        exact nat.le_of_lt_succ hlen}},
    { intros j' hj',
      apply le_of_not_lt, intro hn,
      have := hi ⟨j',hn⟩, simp [sub_left_eq'] at this,
      contradiction }
    end)
,
λ i hi i' hii' hi',begin
have hi_:=leading_entry_eq_sub_left 1 M i hi,
have hi'_:=leading_entry_eq_sub_left 1 M i' hi',
rcases hi with ⟨j,hj⟩, rcases hi' with ⟨j',hj'⟩,
have hh:=hM.2.1 i ⟨j.cast_succ,_⟩ i' hii' ⟨j'.cast_succ,_⟩,
rw [hi_,hi'_] at hh,
exact hh,rw [sub_left_eq'] at hj,exact hj,
rw [sub_left_eq'] at hj',exact hj'
end,
begin
intros i hi,have hi_:=leading_entry_eq_sub_left 1 M i hi,
rw [sub_left_eq',←hi_],
rcases hi with ⟨j,hj⟩,
exact hM.2.2.1 i ⟨j.cast_succ,hj⟩
end,
begin
intros i hi i' hii',
have hi_:=leading_entry_eq_sub_left 1 M i hi,
rw [sub_left_eq',←hi_],
rcases hi with ⟨j,hj⟩,
exact hM.2.2.2 i ⟨j.cast_succ,hj⟩ i' hii'
end⟩ 


lemma left_RREF_of_RREF_add [decidable_eq α] (j : ℕ) (M : matrix (fin m) (fin (n+j)) α) (hM : RREF M) :
RREF (sub_left M) := 
begin
induction j with j hj,
{ rw [sub_left_add_zero],exact hM},
exact hj (λ i j',M i j'.cast_succ) (RREF_of_RREF_succ _ hM),
end

def sub_left_le (M : matrix (fin m) (fin n) α) (p : ℕ) (hp : p ≤ n) : matrix (fin m) (fin p) α :=
M.submatrix id (fin.cast_le hp)

lemma sub_left_le_eq_lam (M : matrix (fin m) (fin n) α) (p : ℕ) (hp : p ≤ n) :
sub_left_le M p hp = λ i j,M i (fin.cast_le hp j) := rfl

lemma sub_left_of_sub_left_le_succ (M : matrix (fin m) (fin n) α) (p : ℕ) (hp : p.succ ≤ n) :
(sub_left_le M (p+1) hp).sub_left = sub_left_le M p (nat.le_of_succ_le hp) := rfl

lemma sub_left_le_eq_zero_of_eq_zero (M : matrix (fin m) (fin n) α) (p : ℕ) (hp : p ≤ n) :
M = 0 → sub_left_le M p hp = 0 := λ h,by simp [sub_left_le_eq_lam];ext i j;exact ext_iff.2 h _ _


def cast_col {p : ℕ} (h : p = n) (M : matrix (fin m) (fin n) α) : matrix (fin m) (fin p) α :=
M.submatrix id (fin.cast h)

lemma cast_col_eq_lam {p : ℕ} (h : p = n) (M : matrix (fin m) (fin n) α) :
  cast_col h M = (λ i j,M i (fin.cast h j)) := rfl

lemma cast_col_cast_eq {p : ℕ} (h : p = n) (M : matrix (fin m) (fin n) α) (i : fin m) (j : fin n):
cast_col h M i (fin.cast h.symm j) = M i j := by simp [cast_col_eq_lam]

lemma sub_left_eq_sub_left_le (p : ℕ) (M : matrix (fin m) (fin (n+p)) α) : 
  M.sub_left = sub_left_le M _ le_self_add := rfl

lemma sub_left_le_eq (M : matrix (fin m) (fin n) α) (p : ℕ) (hp : p ≤ n) (i : fin m) (j : fin p):
sub_left_le M p hp i j = M i (fin.cast_le hp j) := rfl

lemma sub_left_le_eq_sub_left_cast_col  (M : matrix (fin m) (fin n) α) (p : ℕ) (hp : p ≤ n) :
  sub_left_le M p hp = sub_left (cast_col (nat.add_sub_of_le hp) M) := rfl

lemma RREF_cast_col_of_RREF [decidable_eq α] {p : ℕ} (h : p = n) (M : matrix (fin m) (fin n) α) (hM : RREF M) :
RREF (cast_col h M) :=
begin simp [cast_col_eq_lam],
cases hM, induction h, cases hM_right, cases hM_right_right, simp at *, 
fsplit, assumption, 
fsplit, {
intros,rcases hi with ⟨j,hj⟩,rcases hi' with ⟨j',hj'⟩,apply hM_right_left i j hj i' hii' j' hj'
},
fsplit, 
{intros,rcases hi with ⟨j,hj⟩,apply hM_right_right_left i j hj},
{intros,rcases hi with ⟨j,hj⟩,apply hM_right_right_right i j hj i' hii'}
end

lemma left_RREF_of_RREF [decidable_eq α] (M : matrix (fin m) (fin n) α) (hM : RREF M) (j : ℕ) (hj : j ≤ n):
RREF (sub_left_le M j hj) := 
begin
rw [sub_left_le_eq_sub_left_cast_col],
apply left_RREF_of_RREF_add,
apply RREF_cast_col_of_RREF,exact hM
end



lemma elimi_2'' [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) 
  (k:fin m.succ) (h : nonnul_below M k) :
  let i:=first_nonnul_in_first_nonnul_col M k h in
  let j:=first_nonnul_col M k h in
  let M':=(row_add_linear_seq M $ 
    (list.of_fn(λ i':fin (m-i.val),⟨⟨⟨i'.val+i.val.succ,lt_tsub_iff_right.1 ((nat.succ_sub_succ m i.val).symm ▸ i'.property)⟩,i⟩,⟨1,-M ⟨i'.val+i.val.succ,lt_tsub_iff_right.1 ((nat.succ_sub_succ m i.val).symm ▸ i'.property)⟩ j⟩⟩)) ++ 
    [⟨⟨i,i⟩,⟨1/M i j,0⟩⟩]) in
    M' = λ i' j', 
      if j' < j ∨ i' < k then M i' j'
      else
        if i' = i then
          if j' = j then 1
          else M i j'/M i j
        else 
          if j' = j then 0
          else M i' j' - M i' j * M i j'/M i j
      :=
begin
delta,
simp [row_add_linear_seq_append,row_add_linear_ite],
ext i' j',
have := λ M_:matrix (fin m.succ) (fin n) α,row_add_linear_seq_of_fn M_ (m-(first_nonnul_in_first_nonnul_col M k h).val)
      (first_nonnul_in_first_nonnul_col M k h).val.succ _ (λ x,⟨(first_nonnul_in_first_nonnul_col M k h).val,_⟩)
      (λ i,or.inl _) (λ x,1) (λ x,-M ⟨x.val + (first_nonnul_in_first_nonnul_col M k h).val.succ, _⟩ (first_nonnul_col M k h)),
conv at this {simp},simp at this, simp [this],
split_ifs,
{ exfalso,rw h_2 at h_1,exact nat.not_succ_le_self _ h_1.1},
{ exfalso,rw h_2 at h_1,exact nat.not_succ_le_self _ h_1.1},
{ exfalso,rw h_2 at h_1,exact nat.not_succ_le_self _ h_1.1},
{ cases h_3 with h_3' h_3',
  { have hj' : M (first_nonnul_in_first_nonnul_col M k h) j'=0,
    { rw [first_nonnul_col_eq_leading_entry M k h] at h_3',
      apply nul_of_lt_leading_entry,
      apply h_3'},
    simp [hj']},
  { exfalso,apply not_lt_of_le (first_nonnul_is_nonnul M k h).1,
    apply lt_of_le_of_lt _ h_3',
    exact nat.le_of_succ_le h_1.1}
},
{ simp [nat.sub_add_cancel h_1.1,h_4,inv_mul_cancel (first_nonnul_is_nonnul M k h).2]},
{ simp [nat.sub_add_cancel h_1.1],ring},
{ cases h_3 with h_3' h_3',
  { have hj' : M (first_nonnul_in_first_nonnul_col M k h) j'=0,
    { rw [first_nonnul_col_eq_leading_entry M k h] at h_3',
      apply nul_of_lt_leading_entry,
      apply h_3'},
    simp [h_2,hj']},
  { exfalso,apply not_lt_of_le (first_nonnul_is_nonnul M k h).1,
    apply lt_of_le_of_lt _ h_3',
    rw h_2},
},
{ rw h_4,exact inv_mul_cancel (first_nonnul_is_nonnul _ _ h).2},
{ simp [div_eq_inv_mul]},
{ refl},
{ simp at h_1,simp [not_or_distrib] at h_3,cases (le_or_lt (first_nonnul_in_first_nonnul_col M k h).val.succ i') with hic' hic',
  { exfalso,have := h_1 hic',
    rw [←tsub_tsub_assoc,norm_num.sub_nat_pos (nat.succ _) _ 1 rfl] at this,
    exact not_le_of_lt i'.property ((le_tsub_iff_right (@le_of_add_le_right _ _ _ 1 i'.val hic')).mp this),
    exact hic',
    exact nat.le_succ _},
  { rw h_4,exact first_nonnul_is_first _ _ _ _ (nat.lt_of_le_and_ne (nat.le_of_lt_succ hic') (fin.vne_of_ne h_2)) h_3.2,
  }},
{ simp at h_1,simp [not_or_distrib] at h_3,cases (le_or_lt (first_nonnul_in_first_nonnul_col M k h).val.succ i') with hic' hic',
  { exfalso,have := h_1 hic',
    rw [←tsub_tsub_assoc,norm_num.sub_nat_pos (nat.succ _) _ 1 rfl] at this,
    exact not_le_of_lt i'.property ((le_tsub_iff_right (@le_of_add_le_right _ _ _ 1 i'.val hic')).mp this),
    exact hic',
    exact nat.le_succ _},
  { simp [first_nonnul_is_first _ _ h _ (nat.lt_of_le_and_ne (nat.le_of_lt_succ hic') (fin.vne_of_ne h_2)) h_3.2],
  }},
{ rw [tsub_add_eq_add_tsub,nat.add_sub_assoc,norm_num.sub_nat_pos (nat.succ _) _ 1 rfl],
  exact nat.le_succ _, exact nat.le_of_lt_succ (first_nonnul_in_first_nonnul_col M k h).property},
{ exact (first_nonnul_in_first_nonnul_col M k h).property},
{ simp,exact nat.lt_succ_self _},
{ apply nat.lt_succ_of_le, rw [←nat.succ_add_eq_succ_add], apply add_le_of_le_tsub_right_of_le,
  exact nat.le_of_lt_succ (first_nonnul_in_first_nonnul_col M k h).property, exact x.property}
end

lemma elimi_3'' [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) 
  (k:fin m.succ) (h : nonnul_below M k) :
  let i:=first_nonnul_in_first_nonnul_col M k h in
  let j:=first_nonnul_col M k h in
  let M':=(row_add_linear_seq M $ 
    swap_list k i ++ 
    (list.of_fn(λ i':fin (m-i.val),⟨⟨⟨i'.val+i.val.succ,lt_tsub_iff_right.1 ((nat.succ_sub_succ m i.val).symm ▸ i'.property)⟩,i⟩,⟨1,-M ⟨i'.val+i.val.succ,lt_tsub_iff_right.1 ((nat.succ_sub_succ m i.val).symm ▸ i'.property)⟩ j⟩⟩)) ++ 
    [⟨⟨i,i⟩,⟨1/M i j,0⟩⟩]) in 
  M' = λ i' j', 
      if j' < j ∨ i' < k then M i' j'
      else
        if i' = k then
          if j' = j then 1
          else M i j'/M i j
        else 
          if j' = j then 0
          else 
            if i' = i then M k j'
            else M i' j' - M i' j * M i j'/M i j
      :=
begin
simp,
ext i' j',
rw [row_add_linear_seq_append,swap_list_swaps_rows],
have := elimi_2'' M k h,conv at this {simp}, simp at this,
simp [this],split_ifs,
{ cases h_2 with h_2 h_2,
  { rw [h_1,fisrt_nonnul_col_is_first M k h k j' (le_refl k) h_2],
    exact fisrt_nonnul_col_is_first M k h _ j' (first_nonnul_is_nonnul M k h).1 h_2},
  exfalso,exact not_le_of_lt h_2 (first_nonnul_is_nonnul M k h).1},
{ exfalso,cases h_2 with h_2 h_2,
  { rw [h_4] at h_2, exact lt_irrefl _ h_2},
  exact not_le_of_lt h_2 (first_nonnul_is_nonnul M k h).1},
{ exfalso, cases h_2 with h_2 h_2,
  { simp [not_or_distrib] at h_3,
    exact not_le_of_lt h_2 h_3.1},
  exact not_le_of_lt h_2 (first_nonnul_is_nonnul M k h).1},
{ exfalso, cases h_4 with h_4 h_4,
  { rw [h_3] at h_4, exact lt_irrefl _ h_4},
  rw [h_1] at h_4, exact lt_irrefl _ h_4},
{ refl},
{ exfalso, cases h_4 with h_4 h_4,
  { simp [not_or_distrib] at h_2,
    exact not_le_of_lt h_4 h_2.1},
  rw [h_1] at h_4, exact lt_irrefl _ h_4},
{ refl},
{ rw [h_2,fisrt_nonnul_col_is_first M k h k j' (le_refl k) h_3],
  exact (fisrt_nonnul_col_is_first M k h _ j' (first_nonnul_is_nonnul M k h).1 h_3).symm},
{ exact fisrt_nonnul_col_is_first M k h k j' (le_refl k) h_3},
{ refl},
{ exfalso, rw [h_2] at h_1,
  exact h_1 h_4.symm},
{ exfalso, rw [←h_4] at h_2,
  exact h_1 h_2},
{ exfalso, rw [←h_4] at h_2,
  exact h_1 h_2},
{ exfalso, rw [←h_4] at h_2,
  exact h_1 h_2},
{ exfalso, cases h_6 with h_6 h_6,
  { rw [h_5] at h_6, exact lt_irrefl _ h_6},
  rw [h_2] at h_6,exact not_le_of_lt h_6 (first_nonnul_is_nonnul M k h).1},
{ refl},
{ exfalso, cases h_6 with h_6 h_6,
  { exact h_3 h_6},
  rw [h_2] at h_6,exact not_le_of_lt h_6 (first_nonnul_is_nonnul M k h).1},
{ rw [first_nonnul_is_first M k h k _ (le_refl _)],simp,
  simp [not_or_distrib] at h_6,rw [←h_2],exact lt_of_le_of_ne h_6.2 (ne.symm h_1)},
{ refl},
{ refl},
{ refl}

end

lemma elimi_4'' [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) 
  (k:fin m.succ) (h : nonnul_below M k) :
  let j:=first_nonnul_col M k h in
  let i:=first_nonnul_in_first_nonnul_col M k h in
  let M':=(row_add_linear_seq M (eliminating_list M k h)) in
  M' = λ i' j',
    if j' < j then M i' j' 
    else
      if j' = j then 
        if i' = k then 1
        else 0
      else 
        if i' = k then M i j'/M i j
        else 
          if i' = i then M k j'
          else M i' j' - M i' j * M i j'/M i j:=
begin
delta, unfold eliminating_list, delta,
ext i' j', simp [list.append_assoc], rw [row_add_linear_seq_append],
have hfn:= λ M_:matrix (fin m.succ) (fin n) α,row_add_linear_seq_of_fn M_ k.val 0 (by simp;exact le_of_lt k.property)
          (λ x,k) (λ i,or.inr (or.inl (by simp))) (λ x,1) (λ x,-M ⟨x.val, _⟩ (first_nonnul_col M k h)),
have := elimi_3'' M k h, 
simp at this,rw [this],
conv at hfn {simp}, simp at hfn, simp [hfn], clear this hfn,
split_ifs,
{ rw [fisrt_nonnul_col_is_first M k h k j' (le_refl _) h_3],
  simp},
{ exfalso, rw h_5 at h_1,
  exact lt_irrefl _ h_1},
{ simp [h_4]},
{ exfalso, rw h_5 at h_1,
  exact lt_irrefl _ h_1},
{ exfalso, rw h_6 at h_1,
  exact not_le_of_lt h_1 (first_nonnul_is_nonnul M k h).1},
{ ring},
{ exfalso, rw h_3 at h_1,
  exact lt_irrefl _ h_1},
{ exfalso, rw h_3 at h_1,
  exact lt_irrefl _ h_1},
{ exfalso, rw h_3 at h_1,
  exact lt_irrefl _ h_1},
{ exfalso, rw h_3 at h_1,
  exact lt_irrefl _ h_1},
{ exfalso, rw h_4 at h_5,
  exact lt_irrefl _ h_5},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.2 h_1},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.2 h_1},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.2 h_1},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.2 h_1},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.2 h_1},
{ refl},
{ exfalso, cases h_2 with h_2 h_2,
  { exact h_3 h_2},
  exact h_1 h_2},
{ exfalso, cases h_2 with h_2 h_2,
  { exact h_3 h_2},
  exact h_1 h_2},
{ exfalso, cases h_2 with h_2 h_2,
  { exact h_3 h_2},
  exact h_1 h_2},
{ exfalso, cases h_2 with h_2 h_2,
  { exact h_3 h_2},
  exact h_1 h_2},
{ exfalso, cases h_2 with h_2 h_2,
  { exact h_3 h_2},
  exact h_1 h_2},
{ exfalso, rw h_4 at h_5,
  exact lt_irrefl _ h_5},
{ refl},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.1 h_5},
{ refl},
{ exfalso, rw h_4 at h_5,
  exact lt_irrefl _ h_5},
{ refl},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.1 h_6},
{ refl},
{ exfalso,simp [not_or_distrib] at h_2,
  exact not_lt_of_le h_2.1 h_6},
{ refl},
{ exact lt_trans x.property k.property}
end





def first_nul_row [decidable_eq α] [linear_order l] (M : matrix l o α) (h : ∃ i,∀ j,M i j = 0) : l :=
finset.min' (finset.filter (λ i,∀ j,M i j = 0) finset.univ) (let ⟨i,hi⟩:=h in ⟨i,by simpa using hi⟩)

lemma first_nul_row_is_nul [decidable_eq α] [linear_order l] (M : matrix l o α) (h : ∃ i,∀ j,M i j = 0) :
  ∀ j, M (first_nul_row M h) j = 0 :=
begin
have hh: (first_nul_row M  h) ∈ (finset.filter (λ i,∀ j,M i j = 0) finset.univ):=finset.min'_mem _ _,
simpa using hh
end

lemma first_nul_row_is_first [decidable_eq α] [linear_order l] (M : matrix l o α) (h : ∃ i,∀ j,M i j = 0) :
∀ i', (∀ j, M i' j = 0) → first_nul_row M h ≤ i' := 
λ i' hi',finset.min'_le _ _ (by simpa using hi')

lemma first_nul_row_unique [decidable_eq α] [linear_order l] (M : matrix l o α) (h : ∃ i,∀ j,M i j = 0) (i : l):
  (∀ j,M i j = 0) → (∀ i',(∀ j,M i' j = 0) → i ≤ i') → i = first_nul_row M h :=
λ hi hi', le_antisymm (finset.le_min' _ _ _ (λ y hy,hi' _ (by simpa using hy))) (first_nul_row_is_first _ _ _ hi)


lemma RREF_succ_of_RREF' [decidable_eq α] (M : matrix (fin m.succ) (fin (n+1)) α) 
  (hM : RREF M.sub_left) 
  (h :  ∀ hh:∃ i,∀ j:fin n,M i j.cast_succ=0, 
      (M (first_nul_row _ hh) (fin.last n) = 1 ∧ ∀ i,i ≠ first_nul_row _ hh → M i (fin.last n)=0)  ∨ (∀ i, M i (fin.last n)=0) ) :
  RREF M :=
⟨λ i hi i' hi' j,
  begin
    cases lt_or_eq_of_le (fin.le_last j) with hj hj,
    { have := hM.1 i (λ j', hi j'.cast_succ) i' hi' (j.cast_lt hj),
      rwa [sub_left_eq] at this},
    { cases h ⟨i,λ j',hi ⟨j'.val,_⟩⟩ with h' h',
      { have := h'.2 i' (λ hni',not_le_of_lt hi' (by rw hni';exact first_nul_row_is_first _ _ _ (λ j',hi _))),
        simp [←hj] at this,
        exact this},
      { simp [←hj] at h',exact h' _}}
  end,
λ i hi i' hii' hi',
  begin
    cases decidable.em (∃ ii,∀ j:fin n,M ii j.cast_succ=0) with hh hh,
    { cases h hh with h' h',
      { have : fin.last n = leading_entry M (first_nul_row _ hh) ⟨fin.last n,h'.1.symm ▸ one_ne_zero⟩,
          from leading_entry_unique _ _ _ _ (h'.1.symm ▸ one_ne_zero) (λ j' hj',le_of_not_lt 
          (λ hn,by have:=first_nul_row_is_nul _ hh (j'.cast_lt hn);simp at this;exact hj' this)),
        have hi₂ : ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i j.cast_succ) i j ≠ 0,
        { rcases hi with ⟨j,hj⟩,
          cases lt_or_eq_of_le (nat.le_of_lt_succ j.property) with hj' hj',
          { use ⟨j.val,hj'⟩,simp,exact hj},
          { exfalso,rw [(@fin.eq_mk_iff_coe_eq _ _ _ (lt_add_one n)).2 hj'] at hj,
            apply hj, apply h'.2,
            intro hni,
            rcases hi' with ⟨j',hi'⟩,
            apply hi',
            cases lt_or_eq_of_le (fin.le_last j') with hj'' hj'',
            { have := hM.1 i (by simp [hni];exact first_nul_row_is_nul _ hh) i' hii' (j'.cast_lt hj''),
              rwa [sub_left_eq] at this},
            { rw [hj''],
              exact h'.2 _ (by rw ←hni;exact ne_of_gt hii')}}},
        cases (decidable.em (i' = first_nul_row _ hh)) with hi'f hi'f,
        { simp [←hi'f] at this,rw [←this],
          rcases hi₂ with ⟨j,hj⟩,
          simp at hj, apply lt_of_le_of_lt (leading_entry_is_leading M i hi _ hj),
          exact j.property},
        { have hi'₂ : ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i j.cast_succ) i' j ≠ 0,
          { rcases hi' with ⟨j,hi'⟩,
            cases lt_or_eq_of_le (fin.le_last j) with hj hj,
            { use ⟨j.val,hj⟩,simp,exact hi'},
            { exfalso,rw [hj] at hi',
              apply hi', apply h'.2 _ hi'f}},
          have := hM.2.1 i hi₂ i' hii' hi'₂,
          have hli := leading_entry_succ_eq_leading_entry M i hi₂,
          have hli' := leading_entry_succ_eq_leading_entry M i' hi'₂,
          rw [hli,hli'],exact this}},
      { have hi₂ : ∀ ii,(∃ j,M ii j≠0)→ ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i ⟨j.val, nat.lt.step j.property⟩) ii j ≠ 0,
        { intros ii hii,
          rcases hii with ⟨j,hii⟩,
          cases lt_or_eq_of_le (fin.le_last j) with hj hj,
          { use ⟨j.val,hj⟩,simp,exact hii},
          { exfalso, apply hii, simp [←hj] at h',
            exact h' _}},
        have := hM.2.1 i (hi₂ i hi) i' hii' (hi₂ i' hi'),
        have hli := leading_entry_succ_eq_leading_entry M i (hi₂ i hi),
        have hli' := leading_entry_succ_eq_leading_entry M i' (hi₂ i' hi'),
        rw [hli,hli'],exact this
        }},
    { simp at hh,
      have := hM.2.1 i (hh i) i' hii' (hh i'),
      have hli := leading_entry_succ_eq_leading_entry M i (hh i),
      have hli' := leading_entry_succ_eq_leading_entry M i' (hh i'),
      rw [hli,hli'],exact this}
  end,
λ i hi,
  begin
    cases (decidable.em (∃ (i : fin m.succ), ∀ (j : fin n), M i j.cast_succ = 0)) with hh hh,
    { cases h hh with h' h',
      { cases (decidable.em (i = first_nul_row _ hh)) with hif hif,
        { have : fin.last n = leading_entry M (first_nul_row _ hh) ⟨fin.last n,h'.1.symm ▸ one_ne_zero⟩,
            from leading_entry_unique _ _ _ _ (h'.1.symm ▸ one_ne_zero) (λ j' hj',le_of_not_lt 
            (λ hn,by have:=first_nul_row_is_nul _ hh (j'.cast_lt hn);simp at this;exact hj' this)),
          simp_rw [← hif] at this,rw [←this,hif],
          exact h'.1},
        { have hi₂ : ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i j.cast_succ) i j ≠ 0,
          { rcases hi with ⟨j,hi⟩,
            cases lt_or_eq_of_le (fin.le_last j) with hj hj,
            { use ⟨j.val,hj⟩,simp,exact hi},
            { exfalso,rw [hj] at hi,
              apply hi, apply h'.2 _ hif}},
          have hli := leading_entry_succ_eq_leading_entry M i hi₂,
          rw [hli],exact hM.2.2.1 _ _}},
      { have hi₂ : ∀ ii,(∃ j,M ii j≠0)→ ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i j.cast_succ) ii j ≠ 0,
        { intros ii hii,
          rcases hii with ⟨j,hii⟩,
          cases lt_or_eq_of_le (fin.le_last j) with hj hj,
          { use ⟨j.val,hj⟩,simp,exact hii},
          { exfalso, apply hii, simp [←hj] at h',
            exact h' _}},
        have hli := leading_entry_succ_eq_leading_entry M i (hi₂ i hi),
        rw [hli],exact hM.2.2.1 _ _}},
    { simp at hh,
      have hli := leading_entry_succ_eq_leading_entry M i (hh i),
      rw [hli],exact hM.2.2.1 _ _}
  end,
λ i hi i' hi',
  begin
    cases (decidable.em (∃ (i : fin m.succ), ∀ (j : fin n), M i j.cast_succ = 0)) with hh hh,
    { cases h hh with h' h',
      { cases (decidable.em (i = first_nul_row _ hh)) with hif hif,
        { have : fin.last n = leading_entry M (first_nul_row _ hh) ⟨fin.last n,h'.1.symm ▸ one_ne_zero⟩,
            from leading_entry_unique _ _ _ _ (h'.1.symm ▸ one_ne_zero) (λ j' hj',le_of_not_lt 
            (λ hn,by have:=first_nul_row_is_nul _ hh (j'.cast_lt hn);simp at this;exact hj' this)),
          simp_rw [←hif] at this,rw [hif] at hi',rw [←this],
          exact h'.2 _ hi'.symm},
        { have hi₂ : ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i j.cast_succ) i j ≠ 0,
          { rcases hi with ⟨j,hi⟩,
            cases lt_or_eq_of_le (fin.le_last j) with hj hj,
            { use ⟨j.val,hj⟩,simp,exact hi},
            { exfalso,rw [hj] at hi,
              apply hi, apply h'.2 _ hif}},
          have hli := leading_entry_succ_eq_leading_entry M i hi₂,
          rw [hli],exact hM.2.2.2 _ _ _ hi'}},
      { have hi₂ : ∀ ii,(∃ j,M ii j≠0)→ ∃ (j : fin n), (λ (i : fin m.succ) (j : fin n), M i j.cast_succ) ii j ≠ 0,
        { intros ii hii,
          rcases hii with ⟨j,hii⟩,
          cases lt_or_eq_of_le (fin.le_last j) with hj hj,
          { use ⟨j.val,hj⟩,simp,exact hii},
          { exfalso, apply hii, simp [←hj] at h',
            exact h' _}},
        have hli := leading_entry_succ_eq_leading_entry M i (hi₂ i hi),
        rw [hli],exact hM.2.2.2 _ _ _ hi'}},
    { simp at hh,
      have hli := leading_entry_succ_eq_leading_entry M i (hh i),
      rw [hli],exact hM.2.2.2 _ _ _ hi'}
  end⟩


lemma nonnul_row_of_nonnul_below [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k) :
∃ j,M k j ≠ 0 :=
begin
cases decidable.em (∃ j,M k j ≠ 0) with hh hh,
{ exact hh},
simp at hh, rcases h with ⟨i,hki,j,hj⟩,
exfalso,apply hj,apply hM.1 k,apply hh,
apply lt_of_le_of_ne hki,
intro hn,rw ←hn at hj,
exact hj (hh _)
end


lemma nul_bottom_left_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k ) :
∀ i j, k ≤ i → j < leading_entry M k (nonnul_row_of_nonnul_below M hM k h) → M i j = 0 :=
begin 
intros i j' hi hj',
cases (eq_or_lt_of_le hi) with hi' hi',
{ rw ←hi',exact nul_of_lt_leading_entry _ _ (nonnul_row_of_nonnul_below M hM k h) _ hj'},
cases (decidable.em (∀ j:fin n,M i j = 0)) with hi'' hi'',
{ exact hi'' _},
simp at hi'',
exact nul_of_lt_leading_entry _ _ hi'' _ (lt_trans hj' (hM.2.1 _ _ _ hi' _))
end

lemma first_nonnul_col_is_nul_at_k [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k ) :
  M k (first_nonnul_col M k h) ≠ 0 :=
begin
have h₁ := left_RREF_of_RREF M hM (first_nonnul_col M k h).val.succ (first_nonnul_col M k h).property,
have h₁' := left_RREF_of_RREF M hM (first_nonnul_col M k h).val (le_of_lt (first_nonnul_col M k h).property),
cases (decidable.em (∃ i:fin m.succ,k<i ∧ ∀ j:fin (first_nonnul_col M k h).val,M i (j.cast_lt (lt_trans j.property (first_nonnul_col M k h).property)) = 0)) with hh hh,
{ intro h₂,rcases exists_nonnul_in_first_nonnul_col M k h with ⟨i,hi,hii⟩,
  apply hii,cases (eq_or_lt_of_le hi) with hi' hi',
  { rwa [←hi']},
  have := h₁.1 _ _ _ hi' ((first_nonnul_col M k h).cast_lt (nat.lt_succ_self _)),
  simp [sub_left_le_eq_lam,fin.cast_lt] at this,
  exact this,intro j,
  cases (eq_or_lt_of_le (fin.le_last j)) with hj hj,
  { rw [hj],simp [sub_left_le_eq_lam,fin.last],exact h₂},
  apply fisrt_nonnul_col_is_first M k h,
  apply le_refl _,exact hj},
simp at hh,
cases (decidable.em (∃ i:fin m.succ,k<i)) with h₃ h₃,
{ intro h₂,
  rcases h₃ with ⟨i,hi⟩,
  rcases hh i hi with ⟨j,hj⟩,
  apply hj, apply h₁'.1 k _ i hi,
  intro j', apply fisrt_nonnul_col_is_first M k h,
  apply le_refl _,exact j'.property},
simp at h₃,
have h₄ : k = fin.last m, from le_antisymm (nat.le_of_lt_succ k.property) (h₃ _),
simp [h₄],apply first_nonnul_col_last
end

lemma first_nonnul_col_eq_leading_entry_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k ) :
 first_nonnul_col M k h = leading_entry M k (nonnul_row_of_nonnul_below M hM k h) :=
begin
apply leading_entry_unique,
{ exact first_nonnul_col_is_nul_at_k _ hM _ _},
intros j' hj',
apply first_nonnul_col_le,
use k,exact ⟨le_refl _,hj'⟩
end



lemma k_eq_first_nonnul_in_first_nonnul_col [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k ) :
 k = first_nonnul_in_first_nonnul_col M k h :=
begin
have h₁:= first_nonnul_col_eq_leading_entry_of_RREF M hM k h,
rw [first_nonnul_col_eq_leading_entry] at h₁,
cases (eq_or_lt_of_le (first_nonnul_is_nonnul M k h).1) with hh hh,
{ exact hh},
exfalso,
have := hM.2.1 _ (nonnul_row_of_nonnul_below M hM k h) _ hh ⟨first_nonnul_col M k h,(first_nonnul_is_nonnul M k h).2⟩,
rw [h₁] at this,
exact irrefl _ this
end

lemma nonnul_row_of_nonnul_row_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M):
∀ i (h : ∃ j,M i j ≠ 0) i' (hi' : i' ≤ i), ∃ j,M i' j ≠ 0 :=
begin
intros,by_cases hii':i' = i,
{ rwa [←hii'] at h},
by_contra hn,
simp at hn,
have :=hM.1 i' hn i (lt_of_le_of_ne hi' hii'),
exact not_forall.2 h this
end

lemma RREF_of_RREF_succ_row [decidable_eq α] (M : matrix (fin (m+1)) (fin n) α) (hM : RREF M):
RREF M.sub_up :=
⟨λ i hi i' hii' j,hM.1 i.cast_succ hi i'.cast_succ hii' j,
λ i hi i' hii' hi',hM.2.1 i.cast_succ hi i'.cast_succ hii' hi',
λ i hi,hM.2.2.1 i.cast_succ hi,
λ i hi i' hii',hM.2.2.2 i.cast_succ hi i'.cast_succ (λ hn,hii' (fin.cast_succ_inj.1 hn))⟩



lemma le_leading_entry_of_RREF [decidable_eq α] (M : matrix (fin m) (fin n) α) (hM : RREF M):
∀ i (h :∃ j,M i j ≠ 0), i.val ≤ (leading_entry M i h).val :=
begin
intros i h,
induction m with m hm,
{ exfalso,exact nat.not_lt_zero _ i.property},
cases (decidable.em (i = 0)) with h' h',
{ simp [h']},
have h₁ := (nonnul_row_of_nonnul_row_RREF M hM i h (i.pred h') (by simp [fin.le_iff_coe_le_coe];exact nat.pred_le _)),
simp at h₁,
have h₂ := hm (λ i j,M i.cast_succ j) (RREF_of_RREF_succ_row M hM) 
  (i.pred h') h₁,
simp at h₂,
have h₃: ↑(leading_entry (λ (i : fin m), M i.cast_succ) (i.pred h') h₁) < (leading_entry M i h).val,
{ apply hM.2.1,
  apply h₁,simp [fin.lt_iff_coe_lt_coe], apply nat.pred_lt,intro hh,exact h' ((fin.eq_iff_veq _ _).2 hh)},
refine le_trans _ h₃,
refine le_trans _ h₂,
have h₄:i.val = nat.succ (↑i - 1),
{ refine (nat.succ_pred_eq_of_pos _).symm,
  exact nat.pos_of_ne_zero ((not_iff_not.2 (fin.eq_iff_veq _ _)).1 h')},
exact le_refl _
end

lemma nul_bottom_rows_RREF [decidable_eq α]  (M : matrix (fin m) (fin n) α) (hM : RREF M):
∀ i:fin m, i.val ≥ n → ∀ j, M i j = 0 :=
begin
intros i hi,
cases (decidable.em (∃ j,M i j ≠ 0)) with h h,
{ exfalso,
  apply not_le_of_lt (leading_entry M i h).property,
  apply le_trans hi (le_leading_entry_of_RREF M hM i h)},
simp at h,
exact h
end

lemma lt_leading_entry [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : ℕ) (hkm : k < m.succ) (hkn : k < n) (h : nonnul_below M ⟨k,hkm⟩) :
∀ j:fin k, leading_entry M ⟨k,hkm⟩ (nonnul_row_of_nonnul_below M hM ⟨k, hkm⟩ h) > j.cast_lt (lt_trans j.property hkn) :=
begin
intro j,
apply lt_of_lt_of_le ((@fin.lt_iff_coe_lt_coe _ (j.cast_lt (lt_trans j.property hkn)) ⟨k,hkn⟩).2 j.property),
apply fin.le_iff_coe_le_coe.2,
apply le_leading_entry_of_RREF _ hM ⟨k,_⟩
end


lemma exists_sub_left_nul_row_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : ℕ) (hkm : k < m.succ) (hkn : k < n) (h : nonnul_below M ⟨k,hkm ⟩ ) : 
∃ (i : fin m.succ), ∀ (j : fin k), sub_left_le M k (le_of_lt hkn) i j = 0 :=
⟨⟨k,hkm ⟩,λ j,by simp [sub_left_le_eq_lam];exact
  nul_bottom_left_of_RREF _ hM ⟨k,hkm⟩ h _ _ (le_refl _) (lt_leading_entry M hM _ _ hkn _ _)⟩ 

lemma sub_left_le_row_nul_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : ℕ) (hkm : k < m.succ) (hkn : k < n) (h : nonnul_below M ⟨k,hkm ⟩ ): 
∀ (j : fin k), sub_left_le M k (le_of_lt hkn) ⟨k, hkm⟩ j = 0
:=
begin
intro j,
apply nul_bottom_left_of_RREF _ hM ⟨k,hkm⟩ h _ _ (le_refl _) (lt_leading_entry M hM _ _ hkn _ _)
end

lemma nonnul_rows_of_RREF_of_nonnul_below [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k) :
∀ i:fin m.succ, i < k → ∃ j,M i j ≠ 0 :=
begin
intros i hik, by_contra hh, simp at hh,
rcases h with ⟨i',hi',j',hj'⟩,
have := hM.1 i hh i' (lt_of_lt_of_le hik hi'),
exact hj' (this _)
end


lemma eq_eliminating_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k ): 
  M = row_add_linear_seq M (eliminating_list M k h) :=
begin
have he:=elimi_4'' M k h,simp at he,simp [he],
ext i' j',split_ifs,
{ refl},
{ rw [h_3,h_2,first_nonnul_col_eq_leading_entry_of_RREF M hM k h],
  exact hM.2.2.1 k (nonnul_row_of_nonnul_below M hM k h)},
{ rw [h_2,first_nonnul_col_eq_leading_entry_of_RREF M hM k h],
  apply hM.2.2.2,exact ne.symm h_3},
{ rw [←k_eq_first_nonnul_in_first_nonnul_col M hM k h,first_nonnul_col_eq_leading_entry_of_RREF M hM k h,h_3],
  simp [hM.2.2.1 k]},
{ rw [h_4,←k_eq_first_nonnul_in_first_nonnul_col M hM k h]},
{ rw [first_nonnul_col_eq_leading_entry_of_RREF],
  simp [hM.2.2.2 k (nonnul_row_of_nonnul_below M hM k h) i' (ne.symm h_3)],
  exact hM}
end




lemma RREF_eliminating_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (hM : RREF M) (k : fin m.succ) (h : nonnul_below M k ): 
  RREF $ row_add_linear_seq M (eliminating_list M k h) :=
  by rwa [←eq_eliminating_of_RREF M hM k h] 

lemma left_row_add_liner_eq_row_add_linear_left (M : matrix (fin m) (fin n) α) (d : ((fin m) × (fin m)) × (α × α)) (k : ℕ) (hk : k ≤ n):
row_add_linear (sub_left_le M k hk) d.1.1 d.1.2 d.2.1 d.2.2
= sub_left_le (row_add_linear M d.1.1 d.1.2 d.2.1 d.2.2) k hk :=
begin
ext i j,
simp [sub_left_le_eq_lam, row_add_linear_ite]
end

lemma left_row_add_liner_seq_eq_row_add_linear_seq_left (M : matrix (fin m) (fin n) α) (L : list (((fin m) × (fin m)) × (α × α))) (k : ℕ) (hk : k ≤ n):
row_add_linear_seq (sub_left_le M k hk) L = sub_left_le (row_add_linear_seq M L) k hk :=
begin
induction L,
{ simp [row_add_linear_seq_nil]},
rw [row_add_linear_seq_con,row_add_linear_seq_con],
rw [L_ih,left_row_add_liner_eq_row_add_linear_left]
end



lemma eliminating_list_acts_below [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k: fin m.succ)
(h : nonnul_below M k)
(d : (fin m.succ × fin m.succ) × α × α)
(hd : d ∈ eliminating_list M k h)
(hd' : k ≤ d.1.1): k ≤ d.1.2 :=
begin
simp [eliminating_list,list.mem_append] at hd,
cases_type* or,
{ rcases (list.mem_of_fn _ _).1 hd with ⟨i',hi'⟩,
  rw [←hi']},
{ simp [swap_list] at hd,by_cases hk:k = first_nonnul_in_first_nonnul_col M k h,
  { simp [ite_eq_left_iff.2 (λ hhh,absurd hk hhh)] at hd,contradiction},
  { simp [ite_eq_right_iff.2 (λ hhh,absurd hhh hk)] at hd,
    cases_type* or,
    { rw [hd],exact (first_nonnul_is_nonnul _ _ _).1},
    { rw [hd]},
    { rw [hd],exact (first_nonnul_is_nonnul _ _ _).1}}},
{ rcases (list.mem_of_fn _ _).1 hd with ⟨i',hi'⟩,
  rw [←hi'],exact (first_nonnul_is_nonnul _ _ _).1},
{ rw [hd],rwa [hd] at hd'}
end


lemma row_add_linear_seq_eliminating_list_of_sub_left_aux [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k: ℕ) (hkm : k < m.succ) (hkn : k ≤ n)
 (h : nonnul_below M ⟨k,hkm⟩)
 (hh: ∀ (i' : fin m.succ), (⟨k, hkm⟩:fin m.succ) ≤ i' → ∀ (j' : fin k), sub_left_le M k hkn i' j' = 0) (i : fin m.succ) (hi : i < ⟨k,hkm⟩):
 ∀ j:fin k,row_add_linear_seq M (eliminating_list M ⟨k,hkm⟩ h) i (fin.cast_le hkn j) = M i (fin.cast_le hkn j) :=
begin
intro j,
have := elimi_4'' M ⟨k,hkm⟩ h, simp at this,
simp [this],intro h',
exfalso,
have h₁:= lt_first_nonnul_col M ⟨k,hkm⟩ h (fin.cast_le hkn j)
(λ j' hj' i' hi',by simp [fin.le_def] at hj';have := hh i' hi' ⟨j',lt_of_le_of_lt hj' j.property⟩;
simp [sub_left_le_eq_lam] at this;exact this),
exact absurd h₁ (not_lt_of_le h')
end

lemma row_add_linear_seq_eliminating_list_of_sub_left [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k: ℕ) (hkm : k < m.succ) (hkn : k ≤ n)
 (h : nonnul_below M ⟨k,hkm⟩)
 (hh: ∀ (i' : fin m.succ), fin.mk k hkm ≤ i' → ∀ (j' : fin k), sub_left_le M k hkn i' j' = 0) (i : fin m.succ) (hi : i < ⟨k,hkm⟩) :
  ∀ j:fin k,row_add_linear_seq (sub_left_le M k hkn) (eliminating_list M ⟨k,hkm⟩ h) i j= sub_left_le M k hkn i j:=
begin
rw [left_row_add_liner_seq_eq_row_add_linear_seq_left],
exact row_add_linear_seq_eliminating_list_of_sub_left_aux M  k hkm hkn h hh i hi
end


lemma nonnul_below_of_sub_left_le [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k : ℕ) (hkm : k < m.succ) (hkn : k ≤ n) :
nonnul_below (sub_left_le M k hkn) ⟨k,hkm⟩ → nonnul_below M ⟨k,hkm⟩ :=
λ h,let ⟨i,hi,j,hj⟩:=h in ⟨i,hi,fin.cast_le hkn j,hj⟩

lemma first_nonnul_col_sub_left_le [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k : ℕ) (hkm : k < m.succ) (hkn : k ≤ n) 
  (h: nonnul_below (sub_left_le M k hkn) ⟨k,hkm⟩):
fin.cast_le hkn (first_nonnul_col (sub_left_le M k hkn) ⟨k, hkm⟩ h) = first_nonnul_col M ⟨k, hkm⟩ (nonnul_below_of_sub_left_le M k hkm hkn h) :=
first_nonnul_col_is_unique _ _ _ _ (let ⟨i,hik,hi⟩:=exists_nonnul_in_first_nonnul_col _ _ h in ⟨i,hik,hi⟩)
(λ j' hj',or.elim (lt_or_le j'.val k) 
(λ hk,first_nonnul_col_le _ _ h (j'.cast_lt hk) (let ⟨i,hik,hi⟩:=hj' in ⟨i,hik,by simp [sub_left_le_eq_lam,fin.cast_lt];exact hi⟩)) 
(λ hk,fin.le_iff_coe_le_coe.2 (le_trans (le_of_lt (first_nonnul_col (sub_left_le M k hkn) ⟨k, hkm⟩ h).property) hk)))

lemma first_nonnul_in_first_nonnul_col_sub_left_le [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k : ℕ) (hkm : k < m.succ) (hkn : k ≤ n) 
  (h: nonnul_below (sub_left_le M k hkn) ⟨k,hkm⟩):
first_nonnul_in_first_nonnul_col (sub_left_le M k hkn) ⟨k, hkm⟩ h = first_nonnul_in_first_nonnul_col M ⟨k, hkm⟩ (nonnul_below_of_sub_left_le M k hkm hkn h) :=
by simp [sub_left_le_eq_lam,first_nonnul_in_first_nonnul_col,←first_nonnul_col_sub_left_le]

lemma elimi_sub_left_le [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) (k : ℕ) (hkm : k < m.succ) (hkn : k ≤ n) (h: nonnul_below (sub_left_le M k hkn) ⟨k,hkm⟩) :
row_add_linear_seq (sub_left_le M k hkn) (eliminating_list (sub_left_le M k hkn) ⟨k, hkm⟩ h) = sub_left_le (row_add_linear_seq M (eliminating_list M ⟨k,hkm⟩ (nonnul_below_of_sub_left_le M k hkm hkn h))) k hkn :=
begin
have h₁:= elimi_4'' M ⟨k,hkm⟩ (nonnul_below_of_sub_left_le M k hkm hkn h),
have h₂:= elimi_4'' _ ⟨k,hkm⟩ h, 
simp [←first_nonnul_col_sub_left_le,←first_nonnul_in_first_nonnul_col_sub_left_le] at h₁, 
dsimp at h₂,ext i j,
simp [h₁,h₂],simp [sub_left_le_eq_lam]
end

lemma eq_eliminating_of_RREF' [decidable_eq α] (M : matrix (fin m.succ) (fin n) α) 
  (k : ℕ) (hkm : k < m.succ) (hkn : k ≤ n) (hM : RREF (sub_left_le M k hkn)) 
  (h : nonnul_below M ⟨k,hkm⟩ ): 
  row_add_linear_seq (sub_left_le M k hkn) (eliminating_list M ⟨k,hkm⟩ h) = sub_left_le M k hkn :=
begin
cases (decidable.em (nonnul_below (sub_left_le M k hkn) ⟨k,hkm⟩)) with hh hh,
{ nth_rewrite 1 [eq_eliminating_of_RREF _ hM _ hh],rw [elimi_sub_left_le M k hkm hkn hh],
rw [left_row_add_liner_seq_eq_row_add_linear_seq_left]},
simp [nonnul_below] at hh,
ext i j,
by_cases hi:(⟨k, hkm⟩:fin m.succ) ≤ i,
{
have := bot_left_of_nul_block M ⟨k,hkm⟩ ⟨k,nat.lt_succ_iff.mpr hkn⟩
  (λ i' j' hi',by have := hh i' hi' j';rwa [sub_left_le_eq] at this)
  (eliminating_list M ⟨k, hkm⟩ h)
  (λ d hd hd',eliminating_list_acts_below M ⟨k,hkm⟩ h d hd hd') i (fin.cast_le hkn j) hi (by simp [fin.lt_def];exact j.property),
rw [left_row_add_liner_seq_eq_row_add_linear_seq_left,sub_left_le_eq_lam],simp [this],
exact (hh _ hi _).symm
},
{ rw [left_row_add_liner_seq_eq_row_add_linear_seq_left,sub_left_le_eq_lam],simp,simp at hi,
sorry} --TODO
end



lemma RREF_gaussian_aux [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k:ℕ) (hkn:k ≤ n.succ) (hkm : k < m.succ.succ) :
 RREF (sub_left_le (gaussian_elimination_aux M k hkm).1 k hkn):=
begin
revert hkn hkm,
induction k with k' hk',
{ intros hkn hkm,exact RREF_no_col _},
intros, replace hk' := hk' (nat.le_of_succ_le hkn) (nat.lt_of_succ_lt hkm),
sorry --TODO
end


--TODO
lemma RREF_gaussian_aux' [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) (k:ℕ) (hk:k< min n.succ.succ m.succ.succ) :
 RREF (λ (i:fin m.succ) (j : fin k),(gaussian_elimination_aux M k (lt_min_iff.1 hk).2).1 i ⟨j.val,lt_of_lt_of_le j.property (nat.lt_succ_iff.mp (lt_min_iff.1 hk).1)⟩):=
sorry


--TODO
lemma elimi_of_RREF [decidable_eq α] (M : matrix (fin m.succ) (fin n.succ) α) 
  (hM : RREF (λ i (j:fin n.succ),M i ⟨j.val,lt_of_lt_of_le j.property (le_refl _)⟩)) (k : fin m.succ) (h : nonnul_below M k):
  let M' := row_add_linear_seq M (eliminating_list M k h) in
  ∀ hh:∃ i,∀ j:fin n,M' i ⟨j.val,lt_trans j.property (nat.lt_succ_self n)⟩=0, 
      (M' (first_nul_row _ hh) ⟨n,lt_add_one n⟩ = 1 ∧ ∀ i,i ≠ first_nul_row _ hh → M' i ⟨n,lt_add_one n⟩=0)  ∨ (∀ i, M' i ⟨n,lt_add_one n⟩=0) := 
sorry
