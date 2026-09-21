module

public import SynthDom
public import SynthDom.Examples.Delay.Base
public import SynthDom.Examples.Utils.Funext
@[expose] public section

section guarded_streams
open CategoryTheory

gtype Str (A : TYPE) := ν X. [A] × ▸X

gdef Str.cons (A : TYPE) : A → ▸ [Str A] → [Str A] :=
  λ x. λ s. [Str.MK A]ₛ ⟨x, s⟩
gdef Str.hd (A : TYPE) : [Str A] → A :=
  λ t. π₁ ([Str.PROJ A]ₛ t)
gdef Str.tl (A : TYPE) : [Str A] → ▸ [Str A] :=
  λ t. π₂ ([Str.PROJ A]ₛ t)

gtheorem Str.eq_symm (A : TYPE) :
    ∀ x : [Str A]. ∀ y : [Str A]. ((x = y) → (y = x)) := by
    gintro x y H
    grewrite ← H
    grfl

gtheorem Str.prod_eta (A : TYPE) :
    ∀ p : (A × ▸ [Str A]). (p = ⟨π₁ p, π₂ p⟩) := by
    gintro p
    exact ⟨PROVES.eq_def
      (EQ.eta_prod (TYPED.var_explicit (Γ := [[⦃A × ▸[Str A]⦄]]) (nm := `p)
        (0 : Fin 1) (0 : Fin 1)))⟩

gtheorem Str.delay_eta (A : TYPE) :
    ∀ t : ▸ [Str A]. (delay (adv 1 t) = t) := by
    gintro t
    exact ⟨PROVES.eq_def
      (EQ.sym' (EQ.eta_delay (TYPED.var_explicit (Γ := [[⦃▸[Str A]⦄]]) (nm := `t)
        (0 : Fin 1) (0 : Fin 1))))⟩

gdef Str.map (A B : TYPE) : (A → B) → [Str A] → [Str B] :=
  fix μ. λ f. λ s.
    [Str.MK B]ₛ ⟨f (π₁ ([Str.PROJ A]ₛ s)),
                 delay (((adv 1 μ) f) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))⟩

gtheorem Str.beta_test (A : TYPE) :
    ∀ s : [Str A]. ((λ t : [Str A]. [Str.MK A]ₛ ([Str.PROJ A]ₛ t)) s = s) := by
    gintro s
    gsimpl
    gapply (Str.MK_PROJ A) s

gtheorem Str.map_id (A : TYPE) :
    ∀ s : [Str A]. (([Str.map A A]ₛ (λ x : A. x)) s = s) := by
    glöb IH
    gintro s
    gunfold Str.map
    gfix
    gassert Htlf of ((delay _) = delay (adv 1 (π₂ ([Str.PROJ A]ₛ s))))
    · gmono IH as G
      gapply G
    grewrite Htlf
    grewrite (Str.delay_eta A) (π₂ ([Str.PROJ A]ₛ s))
    grewrite ← (Str.prod_eta A)
    gapply (Str.MK_PROJ A)

section composition_law
gtheorem Str.map_cons (A B : TYPE) :
    ∀ f : (A → B). ∀ s : [Str A].
      (([Str.map A B]ₛ f) s
        = [Str.MK B]ₛ ⟨f (π₁ ([Str.PROJ A]ₛ s)),
                       delay (([Str.map A B]ₛ f) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))⟩) := by
    gintro f s
    gunfold Str.map
    gfix
    grfl

gtheorem Str.map_hd (A B : TYPE) :
    ∀ f : (A → B). ∀ s : [Str A].
      (π₁ ([Str.PROJ B]ₛ (([Str.map A B]ₛ f) s)) = f (π₁ ([Str.PROJ A]ₛ s))) := by
    gintro f s
    grewrite (Str.map_cons A B)
    grewrite (Str.PROJ_MK B) ⟨f (π₁ ([Str.PROJ A]ₛ s)),
      delay (([Str.map A B]ₛ f) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))⟩
    gsimpl
    grfl

gtheorem Str.map_tl (A B : TYPE) :
    ∀ f : (A → B). ∀ s : [Str A].
      (π₂ ([Str.PROJ B]ₛ (([Str.map A B]ₛ f) s))
        = delay (([Str.map A B]ₛ f) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))) := by
    gintro f s
    grewrite (Str.map_cons A B)
    grewrite (Str.PROJ_MK B) ⟨f (π₁ ([Str.PROJ A]ₛ s)),
      delay (([Str.map A B]ₛ f) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))⟩
    gsimpl
    grfl

gtheorem Str.map_comp (A B C : TYPE) :
    ∀ f : (A → B). ∀ g : (B → C). ∀ s : [Str A].
      (([Str.map B C]ₛ g) (([Str.map A B]ₛ f) s)
        = ([Str.map A C]ₛ (λ x : A. g (f x))) s) := by
    glöb IH
    gintro f g s
    grewrite (Str.map_cons B C)
    grewrite (Str.map_cons A C)
    grewrite (Str.map_hd A B)
    grewrite (Str.map_tl A B)
    gsimpl
    gcong
    gmono IH as G
    gapply G f  g  (adv 1 (π₂ ([Str.PROJ A]ₛ s)))

end composition_law

gdef Str.rep (A : TYPE) : A → [Str A] :=
  fix μ. λ x. [Str.MK A]ₛ ⟨x, delay ((adv 1 μ) x)⟩

section rep_laws
gtheorem Str.rep_cons (A : TYPE) :
    ∀ x : A.
      (([Str.rep A]ₛ x) = [Str.MK A]ₛ ⟨x, delay (([Str.rep A]ₛ x))⟩) := by
    gintro x
    gunfold Str.rep
    gfix
    grfl

gtheorem Str.hd_rep (A : TYPE) :
    ∀ x : A. (π₁ ([Str.PROJ A]ₛ (([Str.rep A]ₛ x))) = x) := by
    gintro x
    grewrite (Str.rep_cons A)
    grewrite (Str.PROJ_MK A)
    gsimpl
    grfl

gtheorem Str.tl_rep (A : TYPE) :
    ∀ x : A.
      (π₂ ([Str.PROJ A]ₛ (([Str.rep A]ₛ x))) = delay (([Str.rep A]ₛ x))) := by
    gintro x
    grewrite (Str.rep_cons A)
    grewrite (Str.PROJ_MK A)
    gsimpl
    grfl

gtheorem Str.map_rep (A B : TYPE) :
    ∀ f : (A → B). ∀ x : A.
      (([Str.map A B]ₛ f) (([Str.rep A]ₛ x)) = ([Str.rep B]ₛ (f x))) := by
    glöb IH
    gintro f x
    grewrite (Str.map_cons A B)
    grewrite (Str.rep_cons B)
    grewrite (Str.hd_rep A)
    grewrite (Str.tl_rep A)
    gsimpl
    gcong
    gmono IH as G
    gapply G

end rep_laws

gdef Str.zipWith (A B C : TYPE) : (A → B → C) → [Str A] → [Str B] → [Str C] :=
  fix μ. λ g. λ s. λ t.
    [Str.MK C]ₛ ⟨(g (π₁ ([Str.PROJ A]ₛ s))) (π₁ ([Str.PROJ B]ₛ t)),
                 delay ((((adv 1 μ) g) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))
                                       (adv 1 (π₂ ([Str.PROJ B]ₛ t))))⟩

section zip_laws
gtheorem Str.zipWith_cons (A B C : TYPE) :
    ∀ g : (A → B → C). ∀ s : [Str A]. ∀ t : [Str B].
      ((([Str.zipWith A B C]ₛ g) s) t
        = [Str.MK C]ₛ ⟨(g (π₁ ([Str.PROJ A]ₛ s))) (π₁ ([Str.PROJ B]ₛ t)),
            delay ((([Str.zipWith A B C]ₛ g) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))
                                             (adv 1 (π₂ ([Str.PROJ B]ₛ t))))⟩) := by
    gintro g s t
    gunfold Str.zipWith
    gfix
    grfl

gtheorem Str.zip_rep (A B C : TYPE) :
    ∀ g : (A → B → C). ∀ a : A. ∀ b : B.
      ((([Str.zipWith A B C]ₛ g) (([Str.rep A]ₛ a))) (([Str.rep B]ₛ b))
        = ([Str.rep C]ₛ ((g a) b))) := by
    glöb IH
    gintro g a b
    grewrite (Str.zipWith_cons A B C)
    grewrite (Str.rep_cons C)
    grewrite (Str.hd_rep A)
    grewrite (Str.hd_rep B)
    grewrite (Str.tl_rep A)
    grewrite (Str.tl_rep B)
    gsimpl
    gcong
    gmono IH as G
    gapply G g  a  b

gtheorem Str.zip_delay_cong (A B C : TYPE) :
    ∀ g : (A → B → C). ∀ s : [Str A]. ∀ s' : [Str A]. ∀ t : [Str B]. ∀ t' : [Str B].
      ((lift (delay (s = s'))) → ((lift (delay (t = t'))) →
        lift (delay ((([Str.zipWith A B C]ₛ g) s) t = (([Str.zipWith A B C]ₛ g) s') t')))) := by
    gintro g s s' t t' H1 H2
    gmono H1 H2 as E1 E2
    grewrite E1
    grewrite E2
    grfl

end zip_laws

gdef Str.dup (A : TYPE) : [Str A] → [Str (Str A)] :=
  fix μ. λ s.
    [Str.MK (Str A)]ₛ
      ⟨s, delay ((adv 1 μ) (adv 1 (π₂ ([Str.PROJ A]ₛ s))))⟩

section comonad_laws
gtheorem Str.dup_cons (A : TYPE) :
    ∀ s : [Str A].
      (([Str.dup A]ₛ s)
        = [Str.MK (Str A)]ₛ
            ⟨s, delay (([Str.dup A]ₛ (adv 1 (π₂ ([Str.PROJ A]ₛ s)))))⟩) := by
    gintro s
    gunfold Str.dup
    gfix
    grfl

gtheorem Str.extract_dup (A : TYPE) :
    ∀ s : [Str A]. (π₁ ([Str.PROJ (Str A)]ₛ (([Str.dup A]ₛ s))) = s) := by
    gintro s
    grewrite (Str.dup_cons A)
    grewrite (Str.PROJ_MK (Str A))
    gsimpl
    grfl

gtheorem Str.dup_tl (A : TYPE) :
    ∀ s : [Str A].
      (π₂ ([Str.PROJ (Str A)]ₛ (([Str.dup A]ₛ s)))
        = delay (([Str.dup A]ₛ (adv 1 (π₂ ([Str.PROJ A]ₛ s)))))) := by
    gintro s
    grewrite (Str.dup_cons A)
    grewrite (Str.PROJ_MK (Str A))
    gsimpl
    grfl

gtheorem Str.map_extract_dup (A : TYPE) :
    ∀ s : [Str A].
      (([Str.map (Str A) A]ₛ (λ t : [Str A]. π₁ ([Str.PROJ A]ₛ t)))
          (([Str.dup A]ₛ s)) = s) := by
    glöb IH
    gintro s
    grewrite (Str.map_cons (Str A) A)
    grewrite (Str.extract_dup A)
    gassert Htlf of ((delay _) = delay (adv 1 (π₂ ([Str.PROJ A]ₛ s))))
    · grewrite (Str.dup_tl A)
      gsimpl
      gmono IH as G
      gapply G
    grewrite Htlf
    grewrite (Str.delay_eta A) (π₂ ([Str.PROJ A]ₛ s))
    grewrite ← (Str.prod_eta A)
    gapply (Str.MK_PROJ A)

end comonad_laws

section coherence_law
gtheorem Str.map_coherence (A B : TYPE) :
    ∀ f : (A → B). ∀ s : [Str A].
      (([Str.map A B]ₛ f) s
        = (([Str.zipWith ⦃A → B⦄ A B]ₛ
              (λ φ : (A → B). λ x : A. φ x))
            (([Str.rep ⦃A → B⦄]ₛ f))) s) := by
    glöb IH
    gintro f s
    grewrite (Str.map_cons A B)
    grewrite (Str.zipWith_cons ⦃A → B⦄ A B)
    grewrite (Str.hd_rep ⦃A → B⦄)
    grewrite (Str.tl_rep ⦃A → B⦄)
    gsimpl
    gcong
    gmono IH as G
    gapply G

end coherence_law

section coassoc_law
gtheorem Str.dup_coassoc (A : TYPE) :
    ∀ s : [Str A].
      (([Str.map (Str A) (Str (Str A))]ₛ
            [Str.dup A]ₛ) (([Str.dup A]ₛ s))
        = ([Str.dup (Str A)]ₛ) (([Str.dup A]ₛ s))) := by
    glöb IH
    gintro s
    grewrite (Str.map_cons (Str A) (Str (Str A)))
      [Str.dup A]ₛ (([Str.dup A]ₛ s))
    grewrite (Str.dup_cons (Str A))
    grewrite (Str.extract_dup A)
    grewrite (Str.dup_tl A)
    gsimpl
    gcong
    gmono IH as G
    gapply G

end coassoc_law

gdef Str.ap (A B : TYPE) : [Str ⦃A → B⦄] → [Str A] → [Str B] :=
  fix μ. λ u. λ v.
    [Str.MK B]ₛ ⟨(π₁ ([Str.PROJ ⦃A → B⦄]ₛ u)) (π₁ ([Str.PROJ A]ₛ v)),
                 delay ((((adv 1 μ) (adv 1 (π₂ ([Str.PROJ ⦃A → B⦄]ₛ u))))
                                    (adv 1 (π₂ ([Str.PROJ A]ₛ v)))))⟩

gdef Str.idf (A : TYPE) : A → A := λ x. x

gtheorem Str.idf_app (A : TYPE) : ∀ x : A. (([Str.idf A]ₛ x) = x) := by
    gintro x
    gunfold Str.idf
    gsimpl
    grfl

section ap_laws

gtheorem Str.ap_cons (A B : TYPE) :
    ∀ u : [Str ⦃A → B⦄]. ∀ v : [Str A].
      ((([Str.ap A B]ₛ u) v)
        = [Str.MK B]ₛ
            ⟨(π₁ ([Str.PROJ ⦃A → B⦄]ₛ u)) (π₁ ([Str.PROJ A]ₛ v)),
             delay ((([Str.ap A B]ₛ (adv 1 (π₂ ([Str.PROJ ⦃A → B⦄]ₛ u))))
                                    (adv 1 (π₂ ([Str.PROJ A]ₛ v)))))⟩) := by
    gintro u v
    gunfold Str.ap
    gfix
    grfl

gtheorem Str.ap_hd (A B : TYPE) :
    ∀ u : [Str ⦃A → B⦄]. ∀ v : [Str A].
      (π₁ ([Str.PROJ B]ₛ ((([Str.ap A B]ₛ u) v)))
        = (π₁ ([Str.PROJ ⦃A → B⦄]ₛ u)) (π₁ ([Str.PROJ A]ₛ v))) := by
    gintro u v
    grewrite (Str.ap_cons A B)
    grewrite (Str.PROJ_MK B)
      ⟨(π₁ ([Str.PROJ ⦃A → B⦄]ₛ u)) (π₁ ([Str.PROJ A]ₛ v)),
      delay ((([Str.ap A B]ₛ (adv 1 (π₂ ([Str.PROJ ⦃A → B⦄]ₛ u))))
                             (adv 1 (π₂ ([Str.PROJ A]ₛ v)))))⟩
    gsimpl
    grfl

gtheorem Str.ap_tl (A B : TYPE) :
    ∀ u : [Str ⦃A → B⦄]. ∀ v : [Str A].
      (π₂ ([Str.PROJ B]ₛ ((([Str.ap A B]ₛ u) v)))
        = delay ((([Str.ap A B]ₛ (adv 1 (π₂ ([Str.PROJ ⦃A → B⦄]ₛ u))))
                                 (adv 1 (π₂ ([Str.PROJ A]ₛ v)))))) := by
    gintro u v
    grewrite (Str.ap_cons A B)
    grewrite (Str.PROJ_MK B)
      ⟨(π₁ ([Str.PROJ ⦃A → B⦄]ₛ u)) (π₁ ([Str.PROJ A]ₛ v)),
      delay ((([Str.ap A B]ₛ (adv 1 (π₂ ([Str.PROJ ⦃A → B⦄]ₛ u))))
                             (adv 1 (π₂ ([Str.PROJ A]ₛ v)))))⟩
    gsimpl
    grfl

gtheorem Str.ap_id (A : TYPE) :
    ∀ v : [Str A].
      ((([Str.ap A A]ₛ (([Str.rep ⦃A → A⦄]ₛ [Str.idf A]ₛ))) v) = v) := by
    glöb IH
    gintro v
    gunfold Str.ap
    gfix
    grewrite (Str.hd_rep ⦃A → A⦄)
    grewrite (Str.idf_app A)
    gassert Htlf of ((delay _) = delay (adv 1 (π₂ ([Str.PROJ A]ₛ v))))
    · grewrite (Str.tl_rep ⦃A → A⦄)
      gsimpl
      gmono IH as G
      gapply G
    grewrite Htlf
    grewrite (Str.delay_eta A) (π₂ ([Str.PROJ A]ₛ v))
    grewrite ← (Str.prod_eta A)
    gapply (Str.MK_PROJ A)

gtheorem Str.ap_interchange (A B : TYPE) :
    ∀ u : [Str ⦃A → B⦄]. ∀ y : A.
      ((([Str.ap A B]ₛ u) (([Str.rep A]ₛ y)))
        = (([Str.ap ⦃A → B⦄ B]ₛ
              (([Str.rep ⦃(A → B) → B⦄]ₛ (λ f : (A → B). f y))))
            u)) := by
    glöb IH
    gintro u y
    grewrite (Str.ap_cons A B)
    grewrite (Str.ap_cons ⦃A → B⦄ B)
    grewrite (Str.hd_rep A)
    grewrite (Str.hd_rep ⦃(A → B) → B⦄)
    gsimpl
    grewrite (Str.tl_rep A)
    grewrite (Str.tl_rep ⦃(A → B) → B⦄)
    gsimpl
    gcong
    gmono IH as G
    gapply G (adv 1 (π₂ ([Str.PROJ ⦃A → B⦄]ₛ u)))  y

end ap_laws

gdef Str.nth (A U : TYPE) : [Str A] → [Delay U] → [Delay A] :=
  fix μ. λ s. λ c.
    case ([Delay.PROJ U]ₛ c)
      (λ _. [Delay.MK A]ₛ (inl (π₁ ([Str.PROJ A]ₛ s))))
      (λ c'. [Delay.MK A]ₛ
              (inr (delay (((adv 1 μ) (adv 1 (π₂ ([Str.PROJ A]ₛ s)))) (adv 1 c')))))

section nth_laws
gtheorem Str.nth_ret (A U : TYPE) :
    ∀ s : [Str A]. ∀ u : U.
      (([Str.nth A U]ₛ s) ([Delay.MK U]ₛ (inl u))
        = [Delay.MK A]ₛ (inl (π₁ ([Str.PROJ A]ₛ s)))) := by
    gintro s u
    gunfold Str.nth
    gfix
    grewrite (Delay.PROJ_MK U)
    gsimpl
    grfl

gtheorem Str.nth_step (A U : TYPE) :
    ∀ s : [Str A]. ∀ c' : ▸ [Delay U].
      (([Str.nth A U]ₛ s) ([Delay.MK U]ₛ (inr c'))
        = [Delay.MK A]ₛ
            (inr (delay (([Str.nth A U]ₛ (adv 1 (π₂ ([Str.PROJ A]ₛ s)))) (adv 1 c'))))) := by
    gintro s c'
    gunfold Str.nth
    gfix
    grewrite (Delay.PROJ_MK U)
    gsimpl
    grfl

end nth_laws

section pointfree_laws

gtheorem Str.map_id' (A : TYPE) :
    (([Str.map A A]ₛ [idfun A]ₛ) = [idfun (Str A)]ₛ) := by
  gapply (gfunext _ _) ([Str.map A A]ₛ [idfun A]ₛ) ([idfun (Str A)]ₛ)
  gintro s
  gunfold idfun
  gsimpl
  gapply (Str.map_id A) s

gtheorem Str.map_comp' (A B C : TYPE) :
    ∀ f : (A → B). ∀ g : (B → C).
      ((([comp (Str A) (Str B) (Str C)]ₛ ([Str.map B C]ₛ g)) ([Str.map A B]ₛ f))
        = [Str.map A C]ₛ (([comp A B C]ₛ g) f)) := by
  gintro f g
  gapply (gfunext _ _)
    (([comp (Str A) (Str B) (Str C)]ₛ ([Str.map B C]ₛ g)) ([Str.map A B]ₛ f))
    ([Str.map A C]ₛ (([comp A B C]ₛ g) f))
  gintro s
  gunfold comp
  gsimpl
  gapply (Str.map_comp A B C) f g s

gtheorem Str.extract_dup' (A : TYPE) :
    ((([comp (Str A) (Str (Str A)) (Str A)]ₛ
        ([Str.map (Str A) A]ₛ (λ t : [Str A]. π₁ ([Str.PROJ A]ₛ t)))) [Str.dup A]ₛ)
      = [idfun (Str A)]ₛ) := by
  gapply (gfunext _ _)
    (([comp (Str A) (Str (Str A)) (Str A)]ₛ
        ([Str.map (Str A) A]ₛ (λ t : [Str A]. π₁ ([Str.PROJ A]ₛ t)))) [Str.dup A]ₛ)
    ([idfun (Str A)]ₛ)
  gintro s
  gunfold comp
  gunfold idfun
  gsimpl
  gapply (Str.map_extract_dup A) s

gtheorem Str.extract_dup_fn (A : TYPE) :
    ((λ x : [Str A]. π₁ ([Str.PROJ (Str A)]ₛ ([Str.dup A]ₛ x))) = (λ x : [Str A]. x)) := by
  gapply (gfunext _ _)
    (λ x : [Str A]. π₁ ([Str.PROJ (Str A)]ₛ ([Str.dup A]ₛ x))) (λ x : [Str A]. x)
  gintro x
  gapply (Str.extract_dup A)

gtheorem Str.ap_id' (A : TYPE) :
    (([Str.ap A A]ₛ (([Str.rep ⦃A → A⦄]ₛ [Str.idf A]ₛ))) = [idfun (Str A)]ₛ) := by
  gapply (gfunext _ _)
    ([Str.ap A A]ₛ (([Str.rep ⦃A → A⦄]ₛ [Str.idf A]ₛ))) ([idfun (Str A)]ₛ)
  gintro v
  gunfold idfun
  gsimpl
  gapply (Str.ap_id A) v

end pointfree_laws

end guarded_streams

end
