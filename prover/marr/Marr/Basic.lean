import Std

namespace Marran

inductive Mut : Type where
  | val | var | imm
  deriving DecidableEq, Repr

mutual
  inductive Term : Type where
    | lit (n : Nat) : Term
    | var (x : String) : Term
    | lam (x : String) (B : Block) : Term
    | app (t₁ t₂ : Term) : Term
    | pair (t₁ t₂ : Term) : Term
    | arr (ts : List Term) : Term
    | rec_ (fs : List (Mut × String × Term)) : Term
    | prop (t : Term) (l : String) : Term
    | ite (c t e : Term) : Term
    | blk (B : Block) : Term

  inductive Stmt : Type where
    | bind (m : Mut) (x : String) (t : Term) : Stmt
    | rebind (x : String) (t : Term) : Stmt
    | expr (t : Term) : Stmt

  inductive Block : Type where
    | mk (stmts : List Stmt) (body : Term) : Block
end

def freezeMut : Mut → Mut
  | .var => .val
  | m => m

@[simp] theorem freezeMut_val : freezeMut .val = .val := rfl
@[simp] theorem freezeMut_var : freezeMut .var = .val := rfl
@[simp] theorem freezeMut_imm : freezeMut .imm = .imm := rfl

theorem freezeMut_id {m : Mut} (h : m ≠ .var) : freezeMut m = m := by
  cases m <;> simp [freezeMut] at h ⊢

mutual
  def freeze : Term → Term
    | .lit n => .lit n
    | .var x => .var x
    | .lam x B => .lam x (freezeBlock B)
    | .app t₁ t₂ => .app (freeze t₁) (freeze t₂)
    | .pair t₁ t₂ => .pair (freeze t₁) (freeze t₂)
    | .arr ts => .arr (freezeTerms ts)
    | .rec_ fs => .rec_ (freezeFields fs)
    | .prop t l => .prop (freeze t) l
    | .ite c t e => .ite (freeze c) (freeze t) (freeze e)
    | .blk B => .blk (freezeBlock B)

  def freezeTerms : List Term → List Term
    | [] => []
    | t :: ts => freeze t :: freezeTerms ts

  def freezeFields : List (Mut × String × Term) → List (Mut × String × Term)
    | [] => []
    | (m, l, t) :: fs => (freezeMut m, l, freeze t) :: freezeFields fs

  def freezeStmt : Stmt → Stmt
    | .bind m x t => .bind (freezeMut m) x (freeze t)
    | .rebind _ t => .expr (freeze t)
    | .expr t => .expr (freeze t)

  def freezeStmts : List Stmt → List Stmt
    | [] => []
    | s :: ss => freezeStmt s :: freezeStmts ss

  def freezeBlock : Block → Block
    | .mk ss b => .mk (freezeStmts ss) (freeze b)
end

mutual
  def Frozen : Term → Prop
    | .lit _ => True
    | .var _ => True
    | .lam _ B => FrozenBlock B
    | .app t₁ t₂ => Frozen t₁ ∧ Frozen t₂
    | .pair t₁ t₂ => Frozen t₁ ∧ Frozen t₂
    | .arr ts => FrozenTerms ts
    | .rec_ fs => FrozenFields fs
    | .prop t _ => Frozen t
    | .ite c t e => Frozen c ∧ Frozen t ∧ Frozen e
    | .blk B => FrozenBlock B

  def FrozenTerms : List Term → Prop
    | [] => True
    | t :: ts => Frozen t ∧ FrozenTerms ts

  def FrozenFields : List (Mut × String × Term) → Prop
    | [] => True
    | (m, _, t) :: fs => m ≠ .var ∧ Frozen t ∧ FrozenFields fs

  def FrozenStmt : Stmt → Prop
    | .bind .var _ _ => False
    | .bind _ _ t => Frozen t
    | .rebind _ _ => False
    | .expr t => Frozen t

  def FrozenStmts : List Stmt → Prop
    | [] => True
    | s :: ss => FrozenStmt s ∧ FrozenStmts ss

  def FrozenBlock : Block → Prop
    | .mk ss b => FrozenStmts ss ∧ Frozen b
end

mutual
  theorem frozen_freeze : ∀ t : Term, Frozen (freeze t)
    | .lit _ => trivial
    | .var _ => trivial
    | .lam _ B => frozen_freezeBlock B
    | .app t₁ t₂ => ⟨frozen_freeze t₁, frozen_freeze t₂⟩
    | .pair t₁ t₂ => ⟨frozen_freeze t₁, frozen_freeze t₂⟩
    | .arr ts => frozen_freezeTerms ts
    | .rec_ fs => frozen_freezeFields fs
    | .prop t _ => frozen_freeze t
    | .ite c t e => ⟨frozen_freeze c, frozen_freeze t, frozen_freeze e⟩
    | .blk B => frozen_freezeBlock B

  theorem frozen_freezeTerms : ∀ ts : List Term, FrozenTerms (freezeTerms ts)
    | [] => trivial
    | t :: ts => ⟨frozen_freeze t, frozen_freezeTerms ts⟩

  theorem frozen_freezeFields : ∀ fs : List (Mut × String × Term),
      FrozenFields (freezeFields fs)
    | [] => trivial
    | (m, l, t) :: fs => by
      refine ⟨?_, frozen_freeze t, frozen_freezeFields fs⟩
      cases m <;> simp [freezeMut]

  theorem frozen_freezeStmt : ∀ s : Stmt, FrozenStmt (freezeStmt s)
    | .bind .val _ t => frozen_freeze t
    | .bind .var _ t => frozen_freeze t
    | .bind .imm _ t => frozen_freeze t
    | .rebind _ t => frozen_freeze t
    | .expr t => frozen_freeze t

  theorem frozen_freezeStmts : ∀ ss : List Stmt, FrozenStmts (freezeStmts ss)
    | [] => trivial
    | s :: ss => ⟨frozen_freezeStmt s, frozen_freezeStmts ss⟩

  theorem frozen_freezeBlock : ∀ B : Block, FrozenBlock (freezeBlock B)
    | .mk ss b => ⟨frozen_freezeStmts ss, frozen_freeze b⟩
end

#check @Marran.frozen_freeze
#print axioms Marran.frozen_freeze

mutual
  theorem frozen_freeze_id : ∀ t : Term, Frozen t → freeze t = t
    | .lit _, _ => rfl
    | .var _, _ => rfl
    | .lam x B, hB => by
        show Term.lam x (freezeBlock B) = Term.lam x B
        rw [frozen_freezeBlock_id B hB]
    | .app t₁ t₂, h => by
        obtain ⟨h₁, h₂⟩ := h
        show Term.app (freeze t₁) (freeze t₂) = Term.app t₁ t₂
        rw [frozen_freeze_id t₁ h₁, frozen_freeze_id t₂ h₂]
    | .pair t₁ t₂, h => by
        obtain ⟨h₁, h₂⟩ := h
        show Term.pair (freeze t₁) (freeze t₂) = Term.pair t₁ t₂
        rw [frozen_freeze_id t₁ h₁, frozen_freeze_id t₂ h₂]
    | .arr ts, h => by
        show Term.arr (freezeTerms ts) = Term.arr ts
        rw [frozen_freezeTerms_id ts h]
    | .rec_ fs, h => by
        show Term.rec_ (freezeFields fs) = Term.rec_ fs
        rw [frozen_freezeFields_id fs h]
    | .prop t l, ht => by
        show Term.prop (freeze t) l = Term.prop t l
        rw [frozen_freeze_id t ht]
    | .ite c t e, h => by
        obtain ⟨hc, ht, he⟩ := h
        show Term.ite (freeze c) (freeze t) (freeze e) = Term.ite c t e
        rw [frozen_freeze_id c hc, frozen_freeze_id t ht, frozen_freeze_id e he]
    | .blk B, hB => by
        show Term.blk (freezeBlock B) = Term.blk B
        rw [frozen_freezeBlock_id B hB]

  theorem frozen_freezeTerms_id : ∀ ts : List Term, FrozenTerms ts → freezeTerms ts = ts
    | [], _ => rfl
    | t :: ts, h => by
        obtain ⟨ht, hts⟩ := h
        show freeze t :: freezeTerms ts = t :: ts
        rw [frozen_freeze_id t ht, frozen_freezeTerms_id ts hts]

  theorem frozen_freezeFields_id : ∀ fs : List (Mut × String × Term),
      FrozenFields fs → freezeFields fs = fs
    | [], _ => rfl
    | (m, l, t) :: fs, h => by
        obtain ⟨hm, ht, hfs⟩ := h
        show (freezeMut m, l, freeze t) :: freezeFields fs = (m, l, t) :: fs
        rw [freezeMut_id hm, frozen_freeze_id t ht, frozen_freezeFields_id fs hfs]

  theorem frozen_freezeStmt_id : ∀ s : Stmt, FrozenStmt s → freezeStmt s = s
    | .bind .var _ _, h => h.elim
    | .bind .val x t, ht => by
        show Stmt.bind Mut.val x (freeze t) = Stmt.bind Mut.val x t
        rw [frozen_freeze_id t ht]
    | .bind .imm x t, ht => by
        show Stmt.bind Mut.imm x (freeze t) = Stmt.bind Mut.imm x t
        rw [frozen_freeze_id t ht]
    | .rebind _ _, h => h.elim
    | .expr t, ht => by
        show Stmt.expr (freeze t) = Stmt.expr t
        rw [frozen_freeze_id t ht]

  theorem frozen_freezeStmts_id : ∀ ss : List Stmt, FrozenStmts ss → freezeStmts ss = ss
    | [], _ => rfl
    | s :: ss, h => by
        obtain ⟨hs, hss⟩ := h
        show freezeStmt s :: freezeStmts ss = s :: ss
        rw [frozen_freezeStmt_id s hs, frozen_freezeStmts_id ss hss]

  theorem frozen_freezeBlock_id : ∀ B : Block, FrozenBlock B → freezeBlock B = B
    | .mk ss b, h => by
        obtain ⟨hss, hb⟩ := h
        show Block.mk (freezeStmts ss) (freeze b) = Block.mk ss b
        rw [frozen_freezeStmts_id ss hss, frozen_freeze_id b hb]
end

/-! ## 5. Free variables (Lemma 5.1(iii)) -/

def bindingsOf : Stmt → List String
  | .bind _ x _ => [x]
  | .rebind _ _ => []
  | .expr _ => []

def ListSubset (l₁ l₂ : List String) : Prop := ∀ x, x ∈ l₁ → x ∈ l₂

infix:50 " ⊆l " => ListSubset

theorem append_subset {l₁ l₂ l₃ l₄ : List String}
    (h₁ : l₁ ⊆l l₂) (h₂ : l₃ ⊆l l₄) :
    (l₁ ++ l₃) ⊆l (l₂ ++ l₄) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append.mpr (Or.inl (h₁ x hx))
  · exact List.mem_append.mpr (Or.inr (h₂ x hx))

mutual
  def fvAux : List String → Term → List String
    | bound, .lit _ => []
    | bound, .var x => if x ∈ bound then [] else [x]
    | bound, .lam x B => fvBlockAux (x :: bound) B
    | bound, .app t₁ t₂ => fvAux bound t₁ ++ fvAux bound t₂
    | bound, .pair t₁ t₂ => fvAux bound t₁ ++ fvAux bound t₂
    | bound, .arr ts => fvTermsAux bound ts
    | bound, .rec_ fs => fvFieldsAux bound fs
    | bound, .prop t _ => fvAux bound t
    | bound, .ite c t e => fvAux bound c ++ fvAux bound t ++ fvAux bound e
    | bound, .blk B => fvBlockAux bound B

  def fvTermsAux : List String → List Term → List String
    | _, [] => []
    | bound, t :: ts => fvAux bound t ++ fvTermsAux bound ts

  def fvFieldsAux : List String → List (Mut × String × Term) → List String
    | _, [] => []
    | bound, (_, _, t) :: fs => fvAux bound t ++ fvFieldsAux bound fs

  def fvStmtAux : List String → Stmt → List String
    | bound, .bind _ _ t => fvAux bound t
    | bound, .rebind x t => (if x ∈ bound then [] else [x]) ++ fvAux bound t
    | bound, .expr t => fvAux bound t

  def fvBlockAux : List String → Block → List String
    | bound, .mk [] body => fvAux bound body
    | bound, .mk (s :: ss) body =>
        fvStmtAux bound s ++ fvBlockAux (bound ++ bindingsOf s) (.mk ss body)
end

def fv (t : Term) : List String := fvAux [] t

theorem bindingsOf_freezeStmt : ∀ s : Stmt, bindingsOf (freezeStmt s) = bindingsOf s
  | .bind _ _ _ => rfl
  | .rebind _ _ => rfl
  | .expr _ => rfl

mutual
  theorem frozen_fv_aux : ∀ (bound : List String) (t : Term),
      fvAux bound (freeze t) ⊆l fvAux bound t
    | bound, .lit _ => by
        intro x hx; exact hx
    | bound, .var _ => by
        intro y hy; exact hy
    | bound, .lam x B => by
        simp only [freeze, fvAux]
        exact frozen_fv_block_aux (x :: bound) B
    | bound, .app t₁ t₂ => by
        simp only [freeze, fvAux]
        exact append_subset (frozen_fv_aux bound t₁) (frozen_fv_aux bound t₂)
    | bound, .pair t₁ t₂ => by
        simp only [freeze, fvAux]
        exact append_subset (frozen_fv_aux bound t₁) (frozen_fv_aux bound t₂)
    | bound, .arr ts => by
        simp only [freeze, fvAux]
        exact frozen_fv_terms_aux bound ts
    | bound, .rec_ fs => by
        simp only [freeze, fvAux]
        exact frozen_fv_fields_aux bound fs
    | bound, .prop t _ => by
        simp only [freeze, fvAux]
        exact frozen_fv_aux bound t
    | bound, .ite c t e => by
        simp only [freeze, fvAux]
        exact append_subset
          (append_subset (frozen_fv_aux bound c) (frozen_fv_aux bound t))
          (frozen_fv_aux bound e)
    | bound, .blk B => by
        simp only [freeze, fvAux]
        exact frozen_fv_block_aux bound B

  theorem frozen_fv_terms_aux : ∀ (bound : List String) (ts : List Term),
      fvTermsAux bound (freezeTerms ts) ⊆l fvTermsAux bound ts
    | bound, [] => by
        intro x hx; exact hx
    | bound, t :: ts => by
        simp only [freezeTerms, fvTermsAux]
        exact append_subset (frozen_fv_aux bound t) (frozen_fv_terms_aux bound ts)

  theorem frozen_fv_fields_aux : ∀ (bound : List String) (fs : List (Mut × String × Term)),
      fvFieldsAux bound (freezeFields fs) ⊆l fvFieldsAux bound fs
    | bound, [] => by
        intro x hx; exact hx
    | bound, (_, _, t) :: fs => by
        simp only [freezeFields, fvFieldsAux]
        exact append_subset (frozen_fv_aux bound t) (frozen_fv_fields_aux bound fs)

  theorem frozen_fv_stmt_aux : ∀ (bound : List String) (s : Stmt),
      fvStmtAux bound (freezeStmt s) ⊆l fvStmtAux bound s
    | bound, .bind _ _ t => by
        simp only [freezeStmt, fvStmtAux]
        exact frozen_fv_aux bound t
    | bound, .rebind x t => by
        simp only [freezeStmt, fvStmtAux]
        intro y hy
        exact List.mem_append.mpr (Or.inr (frozen_fv_aux bound t y hy))
    | bound, .expr t => by
        simp only [freezeStmt, fvStmtAux]
        exact frozen_fv_aux bound t

  theorem frozen_fv_block_aux : ∀ (bound : List String) (B : Block),
      fvBlockAux bound (freezeBlock B) ⊆l fvBlockAux bound B
    | bound, .mk [] body => by
        rw [show freezeBlock (.mk [] body)
              = Block.mk (freezeStmts []) (freeze body) from rfl,
            show freezeStmts ([] : List Stmt) = [] from rfl]
        simp only [fvBlockAux]
        exact frozen_fv_aux bound body
    | bound, .mk (s :: ss) body => by
        rw [show freezeBlock (.mk (s :: ss) body)
              = Block.mk (freezeStmts (s :: ss)) (freeze body) from rfl,
            show freezeStmts (s :: ss) = freezeStmt s :: freezeStmts ss from rfl]
        simp only [fvBlockAux]
        rw [bindingsOf_freezeStmt s]
        exact append_subset
          (frozen_fv_stmt_aux bound s)
          (frozen_fv_block_aux (bound ++ bindingsOf s) (.mk ss body))
end
/-- Lemma 5.1(iii) — closed-term version. -/
theorem frozen_fv_subset (t : Term) : fv (freeze t) ⊆l fv t :=
  frozen_fv_aux [] t

#print axioms Marran.frozen_freeze_id

end Marran
