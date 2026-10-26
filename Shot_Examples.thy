theory Shot_Examples
  imports Shot
begin

lemma "\<exists>P. P (c::'a)"
  by shot

lemma "(\<forall>x. p x \<longrightarrow> q x) \<Longrightarrow> p a \<Longrightarrow> q a"
  by shot

lemma "(\<exists>x. \<forall>y. r x y) \<longrightarrow> (\<forall>y. \<exists>x. r x y)"
  by shot

lemma "\<exists>f. \<forall>x. f x = (x::'a)"
  by shot

lemma "\<not> (\<forall>x. p x) \<longleftrightarrow> (\<exists>x. \<not> p x)"
  by shot

lemma
  assumes "\<forall>x::nat. f x = g x"
  shows "f 3 = g 3"
  using assms by (shot only:)

lemma
  assumes "A \<subseteq> B" and "x \<in> A"
  shows "x \<in> B"
  using assms by (shot only: subset_eq)

end
