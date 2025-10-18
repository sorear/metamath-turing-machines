x=[]
v_0=y=>x.push("x")
v_1=y=>x.push("y")
v_2=y=>x.push("z")
v_3=y=>x.push("w")
par1=y=>x.push("P")
par2=y=>x.push("Q")
par3=y=>x.push("R")
wel=y=>{z=x.pop();w=x.pop();x.push(w+" e. "+z)}
weq=y=>{z=x.pop();w=x.pop();x.push(w+" = "+z)}
wal=y=>{z=x.pop();w=x.pop();x.push("A. "+w+" "+z)}
wex=y=>{z=x.pop();w=x.pop();x.push("E. "+w+" "+z)}
wim=y=>{z=x.pop();w=x.pop();x.push("( "+w+" -> "+z+" )")}
wa=y=>{z=x.pop();w=x.pop();x.push("( "+w+" /\\ "+z+" )")}
wn=y=>x.push("~ "+x.pop())
select=y=>console.log(x.pop())